{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Ide.Plugin.Tactic.LanguageServer where

import           Control.Arrow
import           Control.Monad
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Maybe
import           Data.Aeson (Value(Object), fromJSON)
import           Data.Aeson.Types (Result(Success, Error))
import           Data.Coerce
import           Data.Foldable (Foldable(toList))
import           Data.Functor ((<&>))
import           Data.Generics.Aliases (mkQ)
import           Data.Generics.Schemes (everything)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe
import           Data.Monoid
import qualified Data.Set as S
import qualified Data.Text as T
import           Data.Traversable
import           Development.IDE (HscEnvEq(hscEnv))
import           Development.IDE.Core.Compile (lookupName)
import           Development.IDE.Core.PositionMapping
import           Development.IDE.Core.RuleTypes
import           Development.IDE.Core.Service (runAction)
import           Development.IDE.Core.Shake (useWithStale, IdeState (..))
import           Development.IDE.GHC.Compat
import           Development.IDE.GHC.Error (realSrcSpanToRange)
import           Development.IDE.Spans.LocalBindings (Bindings, getDefiningBindings)
import           Development.Shake (RuleResult, Action)
import           Development.Shake.Classes
import qualified FastString
import           GhcPlugins (varType, gre_name, ContainsModule(extractModule))
import           Ide.Plugin.Config (PluginConfig(plcConfig))
import qualified Ide.Plugin.Config as Plugin
import           Ide.Plugin.Tactic.Context
import           Ide.Plugin.Tactic.FeatureSet
import           Ide.Plugin.Tactic.GHC
import           Ide.Plugin.Tactic.Judgements
import           Ide.Plugin.Tactic.Range
import           Ide.Plugin.Tactic.TestTypes (cfg_feature_set, TacticCommand)
import           Ide.Plugin.Tactic.Types
import           Ide.PluginUtils (getPluginConfig)
import           Language.LSP.Server (MonadLsp)
import           Language.LSP.Types
import           OccName
import           Prelude hiding (span)
import           SrcLoc (containsSpan)
import           TcRnTypes (tcg_rdr_env, tcg_binds)


tacticDesc :: T.Text -> T.Text
tacticDesc name = "fill the hole using the " <> name <> " tactic"


------------------------------------------------------------------------------
-- | The name of the command for the LS.
tcCommandName :: TacticCommand -> T.Text
tcCommandName = T.pack . show


runIde :: IdeState -> Action a -> IO a
runIde state = runAction "tactic" state


runStaleIde
    :: forall a r
     . ( r ~ RuleResult a
       , Eq a , Hashable a , Binary a , Show a , Typeable a , NFData a
       , Show r, Typeable r, NFData r
       )
    => IdeState
    -> NormalizedFilePath
    -> a
    -> MaybeT IO (r, PositionMapping)
runStaleIde state nfp a = MaybeT $ runIde state $ useWithStale a nfp


------------------------------------------------------------------------------
-- | Get the current feature set from the plugin config.
getFeatureSet :: MonadLsp Plugin.Config m => m FeatureSet
getFeatureSet = do
  pcfg <- getPluginConfig "tactics"
  pure $ case fromJSON $ Object $ plcConfig pcfg of
    Success cfg -> cfg_feature_set cfg
    Error _     -> defaultFeatures


getIdeDynflags
    :: IdeState
    -> NormalizedFilePath
    -> MaybeT IO DynFlags
getIdeDynflags state nfp = do
  -- Ok to use the stale 'ModIface', since all we need is its 'DynFlags'
  -- which don't change very often.
  ((modsum,_), _) <- runStaleIde state nfp GetModSummaryWithoutTimestamps
  pure $ ms_hspp_opts modsum


------------------------------------------------------------------------------
-- | Find the last typechecked module, and find the most specific span, as well
-- as the judgement at the given range.
judgementForHole
    :: IdeState
    -> NormalizedFilePath
    -> Range
    -> FeatureSet
    -> MaybeT IO (Range, Judgement, Context, DynFlags)
judgementForHole state nfp range features = do
  (asts, amapping) <- runStaleIde state nfp GetHieAst
  case asts of
    HAR _ _  _ _ (HieFromDisk _) -> fail "Need a fresh hie file"
    HAR _ hf _ _ HieFresh -> do
      (binds, _) <- runStaleIde state nfp GetBindings
      (tcmod, _) <- runStaleIde state nfp TypeCheck
      (rss, g)   <- liftMaybe $ getSpanAndTypeAtHole amapping range hf
      resulting_range <- liftMaybe $ toCurrentRange amapping $ realSrcSpanToRange rss
      let (jdg, ctx) = mkJudgementAndContext features g binds rss tcmod
      hy' <- fmap buildUserHypothesis $ getOccNameTypes state nfp [mkVarOcc "isSpace"]

      dflags <- getIdeDynflags state nfp
      pure (resulting_range, mergeHypotheses hy' jdg, ctx, dflags)


getOccNameTypes
    :: Foldable t
    => IdeState
    -> NormalizedFilePath
    -> t OccName
    -> MaybeT IO (Map OccName Type)
getOccNameTypes state nfp occs = do
  (tcmod, _) <- runStaleIde state nfp TypeCheck
  (hscenv, _) <- runStaleIde state nfp GhcSessionDeps

  let tcgblenv = tmrTypechecked tcmod
      modul = extractModule tcgblenv
      rdrenv = tcg_rdr_env tcgblenv
  lift $ fmap M.fromList $
    fmap join $ for (toList occs) $ \occ ->
      case lookupOccEnv rdrenv occ of
        Nothing -> pure []
        Just elts -> do
          mvar <- lookupName (hscEnv hscenv) modul $ gre_name $ head elts
          case mvar of
            Just (AnId v) -> pure [ (occ, varType v) ]
            _ -> pure []


buildUserHypothesis :: Map OccName Type -> Hypothesis CType
buildUserHypothesis fns = Hypothesis $ do
  (occ, ty) <- M.toList fns
  pure $ HyInfo occ ImportPrv $ CType ty


mkJudgementAndContext
    :: FeatureSet
    -> Type
    -> Bindings
    -> RealSrcSpan
    -> TcModuleResult
    -> (Judgement, Context)
mkJudgementAndContext features g binds rss tcmod = do
      let tcg  = tmrTypechecked tcmod
          tcs = tcg_binds tcg
          ctx = mkContext features
                  (mapMaybe (sequenceA . (occName *** coerce))
                    $ getDefiningBindings binds rss)
                  tcg
          top_provs = getRhsPosVals rss tcs
          local_hy = spliceProvenance top_provs
                   $ hypothesisFromBindings rss binds
          cls_hy = contextMethodHypothesis ctx
       in ( mkFirstJudgement
              (local_hy <> cls_hy)
              (isRhsHole rss tcs)
              g
          , ctx
          )


getSpanAndTypeAtHole
    :: PositionMapping
    -> Range
    -> HieASTs b
    -> Maybe (Span, b)
getSpanAndTypeAtHole amapping range hf = do
  range' <- fromCurrentRange amapping range
  join $ listToMaybe $ M.elems $ flip M.mapWithKey (getAsts hf) $ \fs ast ->
    case selectSmallestContaining (rangeToRealSrcSpan (FastString.unpackFS fs) range') ast of
      Nothing -> Nothing
      Just ast' -> do
        let info = nodeInfo ast'
        ty <- listToMaybe $ nodeType info
        guard $ ("HsUnboundVar","HsExpr") `S.member` nodeAnnotations info
        pure (nodeSpan ast', ty)


liftMaybe :: Monad m => Maybe a -> MaybeT m a
liftMaybe a = MaybeT $ pure a


spliceProvenance
    :: Map OccName Provenance
    -> Hypothesis a
    -> Hypothesis a
spliceProvenance provs x =
  Hypothesis $ flip fmap (unHypothesis x) $ \hi ->
    overProvenance (maybe id const $ M.lookup (hi_name hi) provs) hi


------------------------------------------------------------------------------
-- | Compute top-level position vals of a function
getRhsPosVals :: RealSrcSpan -> TypecheckedSource -> Map OccName Provenance
getRhsPosVals rss tcs
  = M.fromList
  $ join
  $ maybeToList
  $ getFirst
  $ everything (<>) (mkQ mempty $ \case
      TopLevelRHS name ps
          (L (RealSrcSpan span)  -- body with no guards and a single defn
            (HsVar _ (L _ hole)))
        | containsSpan rss span  -- which contains our span
        , isHole $ occName hole  -- and the span is a hole
        -> First $ do
            patnames <- traverse getPatName ps
            pure $ zip patnames $ [0..] <&> TopLevelArgPrv name
      _ -> mempty
  ) tcs


------------------------------------------------------------------------------
-- | Is this hole immediately to the right of an equals sign?
isRhsHole :: RealSrcSpan -> TypecheckedSource -> Bool
isRhsHole rss tcs = everything (||) (mkQ False $ \case
  TopLevelRHS _ _ (L (RealSrcSpan span) _) -> containsSpan rss span
  _ -> False
  ) tcs

