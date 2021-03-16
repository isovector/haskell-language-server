{-# LANGUAGE TupleSections #-}
module Wingman.Tactics
  ( module Wingman.Tactics
  , runTactic
  ) where

import           ConLike (ConLike(RealDataCon))
import           Control.Applicative (Alternative(empty))
import           Control.Lens ((&), (%~), (<>~))
import           Control.Monad (unless)
import           Control.Monad.Except (throwError)
import           Control.Monad.Reader.Class (MonadReader (ask))
import           Control.Monad.State.Strict (StateT(..), runStateT)
import           Data.Foldable
import           Data.Functor ((<&>))
import           Data.Generics.Labels ()
import           Data.List
import qualified Data.Map as M
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Traversable (for)
import           DataCon
import           Development.IDE.GHC.Compat
import           GHC.Exts
import           GHC.SourceGen.Expr
import           GHC.SourceGen.Overloaded
import           Name (occNameString, occName)
import           Refinery.Tactic
import           Refinery.Tactic.Internal
import           TcType
import           Type hiding (Var)
import           Wingman.CodeGen
import           Wingman.Context
import           Wingman.GHC
import           Wingman.Judgements
import           Wingman.Machinery
import           Wingman.Naming
import           Wingman.Types


applicable_assumptions :: TacticsM [ApplicableTactic]
applicable_assumptions = do
  jdg <- goal
  let ty = jGoal jdg
      hy = jHypothesis jdg
  fmap catMaybes $ for (unHypothesis hy) $ \hi -> do
    subst <- tryUnify (hi_type hi) ty
    pure $ fmap (ApplicableAssumption hi) subst


------------------------------------------------------------------------------
-- | Use something in the hypothesis to fill the hole.
assumption :: TacticsM ()
assumption = do
  as <- applicable_assumptions
  case as of
    [] -> do
      jdg <- goal
      throwError $ CantSynthesize $ jGoal jdg
    _ -> choice $ fmap applyApply as


------------------------------------------------------------------------------
-- | Use something named in the hypothesis to fill the hole.
assume :: HyInfo CType -> TCvSubst -> TacticsM ()
assume hi subst = rule $ const $ do
  let name = hi_name hi
  commitSubst subst
  pure $
    -- This slightly terrible construct is producing a mostly-empty
    -- 'Synthesized'; but there is no monoid instance to do something more
    -- reasonable for a default value.
    (pure (noLoc $ var' name))
      { syn_trace = tracePrim $ "assume " <> occNameString name
      , syn_used_vals = S.singleton name
      }


can_recurse :: TacticsM [ApplicableTactic]
can_recurse = do
  defs <- getCurrentDefinitions
  jdg <- goal
  let g = jGoal jdg
  fmap catMaybes $ for defs $ \(name, ty) -> do
    let (_, _, _, res) = tacticsSplitFunTy $ unCType ty
        hi = HyInfo name RecursivePrv ty
        hy' = recursiveHypothesis defs
    subst <- tryUnify (CType res) g
    pure $ fmap (ApplicableRecursion hy' hi) subst


recursion :: Hypothesis CType -> HyInfo CType -> TCvSubst -> TacticsM ()
-- TODO(sandy): This tactic doesn't fire for the @AutoThetaFix@ golden test,
-- presumably due to running afoul of 'requireConcreteHole'. Look into this!
recursion hy' hi subst = requireConcreteHole $ tracing "recursion" $ do
  markRecursion $ do
    commitSubst subst

    -- Peek allows us to look at the extract produced by this block.
    peek $ \ext -> do
      jdg <- goal
      let pat_vals = jPatHypothesis jdg
      -- Make sure that the recursive call contains at least one already-bound
      -- pattern value. This ensures it is structurally smaller, and thus
      -- suggests termination.
      unless (any (flip M.member pat_vals) $ syn_used_vals ext) empty

    localTactic
        (maybe empty applyApply =<< mkApply hi)
        (introduce hy')
      <@> fmap (localTactic assumption . filterPosition (hi_name hi)) [0..]


------------------------------------------------------------------------------
-- | Introduce a lambda binding every variable.
intros :: TacticsM ()
intros = rule $ \jdg -> do
  let g  = jGoal jdg
  ctx <- ask
  case tcSplitFunTys $ unCType g of
    ([], _) -> cut
    (as, b) -> do
      vs <- mkManyGoodNames (hyNamesInScope $ jEntireHypothesis jdg) as
      let top_hole = isTopHole ctx jdg
          hy' = lambdaHypothesis top_hole $ zip vs $ coerce as
          jdg' = introduce hy'
               $ withNewGoal (CType b) jdg
      ext <- newSubgoal jdg'
      pure $
        ext
          & #syn_trace %~
                rose ("intros {" <> intercalate ", " (fmap show vs) <> "}")
                  . pure
          & #syn_scoped <>~ hy'
          & #syn_val     %~ noLoc . lambda (fmap bvar' vs) . unLoc


------------------------------------------------------------------------------
-- | Case split, and leave holes in the matches.
destructAuto :: HyInfo CType -> TacticsM ()
destructAuto hi = requireConcreteHole $ tracing "destruct(auto)" $ do
  jdg <- goal
  let subtactic = rule $ destruct' (const subgoal) hi
  case isPatternMatch $ hi_provenance hi of
    True ->
      pruning subtactic $ \jdgs ->
        let getHyTypes = S.fromList . fmap hi_type . unHypothesis . jHypothesis
            new_hy = foldMap getHyTypes jdgs
            old_hy = getHyTypes jdg
        in case S.null $ new_hy S.\\ old_hy of
              True  -> Just $ UnhelpfulDestruct $ hi_name hi
              False -> Nothing
    False -> subtactic


------------------------------------------------------------------------------
-- | Case split, and leave holes in the matches.
destruct :: HyInfo CType -> TacticsM ()
destruct hi = requireConcreteHole $ tracing "destruct(user)" $
  rule $ destruct' (const subgoal) hi


------------------------------------------------------------------------------
-- | Case split, using the same data constructor in the matches.
homo :: HyInfo CType -> TacticsM ()
homo = requireConcreteHole . tracing "homo" . rule . destruct' (\dc jdg ->
  buildDataCon jdg dc $ snd $ splitAppTys $ unCType $ jGoal jdg)


------------------------------------------------------------------------------
-- | LambdaCase split, and leave holes in the matches.
destructLambdaCase :: TacticsM ()
destructLambdaCase =
  tracing "destructLambdaCase" $ rule $ destructLambdaCase' (const subgoal)


------------------------------------------------------------------------------
-- | LambdaCase split, using the same data constructor in the matches.
homoLambdaCase :: TacticsM ()
homoLambdaCase =
  tracing "homoLambdaCase" $
    rule $ destructLambdaCase' $ \dc jdg ->
      buildDataCon jdg dc
        . snd
        . splitAppTys
        . unCType
        $ jGoal jdg


data ApplicableTactic
  = ApplicableApply OccName [Type] TCvSubst
  | ApplicableAssumption (HyInfo CType) TCvSubst
  | ApplicableSplit [DataCon] [Type]
  | ApplicableRecursion (Hypothesis CType) (HyInfo CType) TCvSubst


applicable_applies :: TacticsM [ApplicableTactic]
applicable_applies = do
  jdg <- goal
  let hy = jHypothesis jdg
  fmap catMaybes
    $ for (filter (isFunction . unCType . hi_type) $ unHypothesis hy)
    $ mkApply


mkApply :: HyInfo CType -> TacticsM (Maybe ApplicableTactic)
mkApply hi = do
  jdg <- goal
  let g = jGoal jdg
      ty = unCType $ hi_type hi
  ty' <- freshTyvars ty
  let (_, _, args, ret) = tacticsSplitFunTy ty'
  subst <- tryUnify g (CType ret)
  pure $ fmap (ApplicableApply (hi_name hi) args) subst


apply :: TacticsM ()
apply = do
  applies <- applicable_applies
  choice $ applies <&> \(ApplicableApply a b c) ->
    apply' a b c


applyApply :: ApplicableTactic -> TacticsM ()
applyApply (ApplicableApply a b c) = apply' a b c
applyApply (ApplicableAssumption a b) = assume a b
applyApply (ApplicableSplit a b) = splitAuto a b
applyApply (ApplicableRecursion a b c) = recursion a b c


apply' :: OccName -> [Type] -> TCvSubst -> TacticsM ()
apply' func args subst =
  requireConcreteHole $ tracing ("apply' " <> show func) $
    rule $ \jdg -> do
      commitSubst subst
      ext
          <- fmap unzipTrace
          $ traverse ( newSubgoal
                      . blacklistingDestruct
                      . flip withNewGoal jdg
                      . CType
                      ) args
      pure $
        ext
          & #syn_used_vals %~ S.insert func
          & #syn_val       %~ noLoc . foldl' (@@) (var' func) . fmap unLoc


can_split :: TacticsM (Maybe (ApplicableTactic))
can_split = do
  jdg <- goal
  let g = jGoal jdg
  pure $ fmap (uncurry ApplicableSplit) $ tacticsGetDataCons $ unCType g


------------------------------------------------------------------------------
-- | Choose between each of the goal's data constructors.
split :: TacticsM ()
split = tracing "split(user)" $ do
  jdg <- goal
  let g = jGoal jdg
  case tacticsGetDataCons $ unCType g of
    Nothing -> empty
    Just (dcs, _) -> choice $ fmap splitDataCon dcs


------------------------------------------------------------------------------
-- | Choose between each of the goal's data constructors. Different than
-- 'split' because it won't split a data con if it doesn't result in any new
-- goals.
splitAuto :: [DataCon] -> [Type] -> TacticsM ()
splitAuto dcs _ = requireConcreteHole $ tracing "split(auto)" $ do
  jdg <- goal
  case isSplitWhitelisted jdg of
    True -> choice $ fmap splitDataCon dcs
    False -> do
      choice $ flip fmap dcs $ \dc -> requireNewHoles $
        splitDataCon dc


------------------------------------------------------------------------------
-- | Like 'split', but only works if there is a single matching data
-- constructor for the goal.
splitSingle :: TacticsM ()
splitSingle = tracing "splitSingle" $ do
  jdg <- goal
  let g = jGoal jdg
  case tacticsGetDataCons $ unCType g of
    Just ([dc], _) -> do
      splitDataCon dc
    _ -> empty


------------------------------------------------------------------------------
-- | Allow the given tactic to proceed if and only if it introduces holes that
-- have a different goal than current goal.
requireNewHoles :: TacticsM () -> TacticsM ()
requireNewHoles m = do
  jdg <- goal
  pruning m $ \jdgs ->
    case null jdgs || any (/= jGoal jdg) (fmap jGoal jdgs) of
      True  -> Nothing
      False -> Just NoProgress


------------------------------------------------------------------------------
-- | Attempt to instantiate the given ConLike to solve the goal.
--
-- INVARIANT: Assumes the given ConLike is appropriate to construct the type
-- with.
splitConLike :: ConLike -> TacticsM ()
splitConLike dc =
  requireConcreteHole $ tracing ("splitDataCon:" <> show dc) $ rule $ \jdg -> do
    let g = jGoal jdg
    case splitTyConApp_maybe $ unCType g of
      Just (_, apps) -> do
        buildDataCon (unwhitelistingSplit jdg) dc apps
      Nothing -> cut


------------------------------------------------------------------------------
-- | Attempt to instantiate the given data constructor to solve the goal.
--
-- INVARIANT: Assumes the given datacon is appropriate to construct the type
-- with.
splitDataCon :: DataCon -> TacticsM ()
splitDataCon = splitConLike . RealDataCon


------------------------------------------------------------------------------
-- | Perform a case split on each top-level argument. Used to implement the
-- "Destruct all function arguments" action.
destructAll :: TacticsM ()
destructAll = do
  jdg <- goal
  let args = fmap fst
           $ sortOn (Down . snd)
           $ mapMaybe (\(hi, prov) ->
              case prov of
                TopLevelArgPrv _ idx _ -> pure (hi, idx)
                _ -> Nothing
                )
           $ fmap (\hi -> (hi, hi_provenance hi))
           $ unHypothesis
           $ jHypothesis jdg
  for_ args destruct


--------------------------------------------------------------------------------
-- | User-facing tactic to implement "Use constructor <x>"
userSplit :: OccName -> TacticsM ()
userSplit occ = do
  jdg <- goal
  let g = jGoal jdg
  -- TODO(sandy): It's smelly that we need to find the datacon to generate the
  -- code action, send it as a string, and then look it up again. Can we push
  -- this over LSP somehow instead?
  case splitTyConApp_maybe $ unCType g of
    Just (tc, _) -> do
      case find (sloppyEqOccName occ . occName . dataConName)
             $ tyConDataCons tc of
        Just dc -> splitDataCon dc
        Nothing -> empty
    Nothing -> empty


------------------------------------------------------------------------------
-- | @matching f@ takes a function from a judgement to a @Tactic@, and
-- then applies the resulting @Tactic@.
matching :: (Judgement -> TacticsM ()) -> TacticsM ()
matching f = TacticT $ StateT $ \s -> runStateT (unTacticT $ f s) s


attemptOn :: (Judgement -> [a]) -> (a -> TacticsM ()) -> TacticsM ()
attemptOn getNames tac = matching (choice . fmap (\s -> tac s) . getNames)


localTactic :: TacticsM a -> (Judgement -> Judgement) -> TacticsM a
localTactic t f = do
  TacticT $ StateT $ \jdg ->
    runStateT (unTacticT t) $ f jdg


refine :: TacticsM ()
refine = do
  try' intros
  try' splitSingle
  try' intros


auto' :: Int -> TacticsM ()
auto' 0 = do
  jdg <- goal
  throwError $ CantSynthesize $ jGoal jdg
auto' n = do
  let loop = auto' (n - 1)
  try intros

  splittable <- can_split
  applies    <- applicable_applies
  as         <- applicable_assumptions
  recs       <- can_recurse

  let available = maybeToList splittable <> applies <> as <> recs

  choice
    [ choice $ available <&> \app -> do
        applyApply app
        loop
    , overAlgebraicTerms $ \aname -> do
        destructAuto aname
        loop
    ]

overFunctions :: (HyInfo CType -> TacticsM ()) -> TacticsM ()
overFunctions =
  attemptOn $ filter (isFunction . unCType . hi_type)
           . unHypothesis
           . jHypothesis

overAlgebraicTerms :: (HyInfo CType -> TacticsM ()) -> TacticsM ()
overAlgebraicTerms =
  attemptOn $ filter (isJust . algebraicTyCon . unCType . hi_type)
            . unHypothesis
            . jHypothesis


allNames :: Judgement -> Set OccName
allNames = hyNamesInScope . jHypothesis

