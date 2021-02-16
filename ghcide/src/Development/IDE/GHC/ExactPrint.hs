{-# LANGUAGE CPP                #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE TypeFamilies       #-}

module Development.IDE.GHC.ExactPrint
    ( Graft(..),
      graft,
      graftWithoutParentheses,
      graftDecls,
      graftDeclsWithM,
      annotate,
      hoistGraft,
      graftWithM,
      graftWithSmallestM,
      graftSmallestDecls,
      graftSmallestDeclsWithM,
      transform,
      transformM,
      useAnnotatedSource,
      annotateParsedSource,
      getAnnotatedParsedSourceRule,
      GetAnnotatedParsedSource(..),
      ASTElement (..),
      ExceptStringT (..),
      Annotated(..),
      TransformT,
      Anns,
      Annotate,
    )
where

import BasicTypes (appPrec)
import Control.Applicative (Alternative)
import Control.Monad
import qualified Control.Monad.Fail as Fail
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Zip
import qualified Data.DList as DL
import Data.Either.Extra (mapLeft)
import Data.Functor.Classes
import Data.Functor.Contravariant
import qualified Data.Text as T
import Development.IDE.Core.RuleTypes
import Development.IDE.Core.Service (runAction)
import Development.IDE.Core.Shake
import Development.IDE.GHC.Compat hiding (parseExpr)
import Development.IDE.Types.Location
import Development.Shake (RuleResult, Rules)
import Development.Shake.Classes
import qualified GHC.Generics as GHC
import Generics.SYB
import Ide.PluginUtils
import Language.Haskell.GHC.ExactPrint
import Language.Haskell.GHC.ExactPrint.Parsers
import Language.Haskell.LSP.Types
import Language.Haskell.LSP.Types.Capabilities (ClientCapabilities)
import Outputable (Outputable, ppr, showSDoc)
import Retrie.ExactPrint hiding (parseDecl, parseExpr, parsePattern, parseType)
import Parser (parseIdentifier)
import Data.List (isPrefixOf)
import Data.Traversable (for)
#if __GLASGOW_HASKELL__ == 808
import Control.Arrow
#endif
#if __GLASGOW_HASKELL__ > 808
import Bag (listToBag)
import ErrUtils (mkErrMsg)
import Outputable (text, neverQualify)
#endif


------------------------------------------------------------------------------

data GetAnnotatedParsedSource = GetAnnotatedParsedSource
  deriving (Eq, Show, Typeable, GHC.Generic)

instance Hashable GetAnnotatedParsedSource
instance NFData GetAnnotatedParsedSource
instance Binary GetAnnotatedParsedSource
type instance RuleResult GetAnnotatedParsedSource = Annotated ParsedSource

-- | Get the latest version of the annotated parse source with comments.
getAnnotatedParsedSourceRule :: Rules ()
getAnnotatedParsedSourceRule = define $ \GetAnnotatedParsedSource nfp -> do
  pm <- use GetParsedModuleWithComments nfp
  return ([], fmap annotateParsedSource pm)

annotateParsedSource :: ParsedModule -> Annotated ParsedSource
annotateParsedSource = fixAnns

useAnnotatedSource ::
  String ->
  IdeState ->
  NormalizedFilePath ->
  IO (Maybe (Annotated ParsedSource))
useAnnotatedSource herald state nfp =
    runAction herald state (use GetAnnotatedParsedSource nfp)
------------------------------------------------------------------------------

{- | A transformation for grafting source trees together. Use the semigroup
 instance to combine 'Graft's, and run them via 'transform'.
-}
newtype Graft m a = Graft
    { runGraft :: DynFlags -> a -> TransformT m a
    }

hoistGraft :: (forall x. m x -> n x) -> Graft m a -> Graft n a
hoistGraft h (Graft f) = Graft (fmap (hoistTransform h) . f)

newtype ExceptStringT m a = ExceptStringT {runExceptString :: ExceptT String m a}
    deriving newtype
        ( MonadTrans
        , Monad
        , Functor
        , Applicative
        , Alternative
        , Foldable
        , Contravariant
        , MonadIO
        , Eq1
        , Ord1
        , Show1
        , Read1
        , MonadZip
        , MonadPlus
        , Eq
        , Ord
        , Show
        , Read
        )

instance Monad m => Fail.MonadFail (ExceptStringT m) where
    fail = ExceptStringT . ExceptT . pure . Left

instance Monad m => Semigroup (Graft m a) where
    Graft a <> Graft b = Graft $ \dflags -> a dflags >=> b dflags

instance Monad m => Monoid (Graft m a) where
    mempty = Graft $ const pure

------------------------------------------------------------------------------

-- | Convert a 'Graft' into a 'WorkspaceEdit'.
transform ::
    DynFlags ->
    ClientCapabilities ->
    Uri ->
    Graft (Either String) ParsedSource ->
    Annotated ParsedSource ->
    Either String WorkspaceEdit
transform dflags ccs uri f a = do
    let src = printA a
    a' <- transformA a $ runGraft f dflags
    let res = printA a'
    pure $ diffText ccs (uri, T.pack src) (T.pack res) IncludeDeletions

------------------------------------------------------------------------------

-- | Convert a 'Graft' into a 'WorkspaceEdit'.
transformM ::
    Monad m =>
    DynFlags ->
    ClientCapabilities ->
    Uri ->
    Graft (ExceptStringT m) ParsedSource ->
    Annotated ParsedSource ->
    m (Either String WorkspaceEdit)
transformM dflags ccs uri f a = runExceptT $
    runExceptString $ do
        let src = printA a
        a' <- transformA a $ runGraft f dflags
        let res = printA a'
        pure $ diffText ccs (uri, T.pack src) (T.pack res) IncludeDeletions

------------------------------------------------------------------------------

{- | Construct a 'Graft', replacing the node at the given 'SrcSpan' with the
 given 'LHSExpr'. The node at that position must already be a 'LHsExpr', or
 this is a no-op.
-}
graft ::
    forall ast a.
    (Data a, ASTElement ast) =>
    SrcSpan ->
    Located ast ->
    Graft (Either String) a
graft dst = graftWithoutParentheses dst . maybeParensAST

-- | Like 'graft', but trusts that you have correctly inserted the parentheses
-- yourself. If you haven't, the resulting AST will not be valid!
graftWithoutParentheses ::
    forall ast a.
    (Data a, ASTElement ast) =>
    SrcSpan ->
    Located ast ->
    Graft (Either String) a
graftWithoutParentheses dst val = Graft $ \dflags a -> do
    (anns, val') <- annotate dflags val
    modifyAnnsT $ mappend anns
    pure $
        everywhere'
            ( mkT $
                \case
                    (L src _ :: Located ast) | src == dst -> val'
                    l -> l
            )
            a


------------------------------------------------------------------------------
-- | 'parseDecl' fails to parse decls that span multiple lines at the top
-- layout --- eg. things like:
--
-- @
-- not True = False
-- not False = True
-- @
--
-- This function splits up each top-layout declaration, parses them
-- individually, and then merges them back into a single decl.
parseDecls :: DynFlags -> FilePath -> String -> ParseResult (LHsDecl GhcPs)
parseDecls dflags fp str = do
  let mono_decls = fmap unlines $ groupByFirstLine $ lines str
  decls <-
    for (zip [id @Int 0..] mono_decls) $ \(ix, line) ->
      parseDecl dflags (fp <> show ix) line
  mergeDecls decls


------------------------------------------------------------------------------
-- | Combine decls together. See 'parseDecl' for more information.
mergeDecls :: [(Anns, LHsDecl GhcPs)] -> ParseResult (LHsDecl GhcPs)
mergeDecls [x] = pure x
mergeDecls ((anns,  L _ (ValD ext fb@FunBind{fun_matches = mg@MG {mg_alts = L _ alts}}))
          -- Since 'groupByFirstLine' separates matches, we are guaranteed to
          -- only have a single alternative here. We want to add it to 'alts'
          -- above.
          : (anns', L _ (ValD _ FunBind{fun_matches = MG {mg_alts = L _ [alt]}}))
          : decls) =
  mergeDecls $
    ( anns <> setPrecedingLines alt 1 0 anns'
    , noLoc $ ValD ext $ fb
        { fun_matches = mg { mg_alts = noLoc $ alts <> [alt] }
        }
    ) : decls
mergeDecls _ = throwParseError "mergeDecls: attempted to merge something that wasn't a ValD FunBind"


throwParseError :: String -> ParseResult a
#if __GLASGOW_HASKELL__ > 808
throwParseError
  = Left . listToBag . pure . mkErrMsg unsafeGlobalDynFlags noSrcSpan neverQualify . text
#else
throwParseError = Left . (noSrcSpan, )
#endif


------------------------------------------------------------------------------
-- | Groups strings by the Haskell top-layout rules, assuming each element of
-- the list corresponds to a line. For example, the list
--
-- @["a", " a1", " a2", "b", " b1"]@
--
-- will be grouped to
--
-- @[["a", " a1", " a2"], ["b", " b1"]]@
groupByFirstLine :: [String] -> [[String]]
groupByFirstLine [] = []
groupByFirstLine (str : strs) =
  let (same, diff) = span (isPrefixOf " ") strs
   in (str : same) : groupByFirstLine diff


------------------------------------------------------------------------------

graftWithM ::
    forall ast m a.
    (Fail.MonadFail m, Data a, ASTElement ast) =>
    SrcSpan ->
    (Located ast -> TransformT m (Maybe (Located ast))) ->
    Graft m a
graftWithM dst trans = Graft $ \dflags a -> do
    everywhereM'
        ( mkM $
            \case
                val@(L src _ :: Located ast)
                    | src == dst -> do
                        mval <- trans val
                        case mval of
                            Just val' -> do
                                (anns, val'') <-
                                    hoistTransform (either Fail.fail pure) $
                                        annotate dflags $ maybeParensAST val'
                                modifyAnnsT $ mappend anns
                                pure val''
                            Nothing -> pure val
                l -> pure l
        )
        a

graftWithSmallestM ::
    forall ast m a.
    (Fail.MonadFail m, Data a, ASTElement ast) =>
    SrcSpan ->
    (Located ast -> TransformT m (Maybe (Located ast))) ->
    Graft m a
graftWithSmallestM dst trans = Graft $ \dflags a -> do
    everywhereM'
        ( mkM $
            \case
                val@(L src _ :: Located ast)
                    | dst `isSubspanOf` src -> do
                        mval <- trans val
                        case mval of
                            Just val' -> do
                                (anns, val'') <-
                                    hoistTransform (either Fail.fail pure) $
                                        annotate dflags $ maybeParensAST val'
                                modifyAnnsT $ mappend anns
                                pure val''
                            Nothing -> pure val
                l -> pure l
        )
        a

graftDecls ::
    forall a.
    (HasDecls a) =>
    SrcSpan ->
    [LHsDecl GhcPs] ->
    Graft (Either String) a
graftDecls dst decs0 = Graft $ \dflags a -> do
    decs <- forM decs0 $ \decl -> do
        (anns, decl') <- annotateDecl dflags decl
        modifyAnnsT $ mappend anns
        pure decl'
    let go [] = DL.empty
        go (L src e : rest)
            | src == dst = DL.fromList decs <> DL.fromList rest
            | otherwise = DL.singleton (L src e) <> go rest
    modifyDeclsT (pure . DL.toList . go) a

graftSmallestDecls ::
    forall a.
    (HasDecls a) =>
    SrcSpan ->
    [LHsDecl GhcPs] ->
    Graft (Either String) a
graftSmallestDecls dst decs0 = Graft $ \dflags a -> do
    decs <- forM decs0 $ \decl -> do
        (anns, decl') <- annotateDecl dflags decl
        modifyAnnsT $ mappend anns
        pure decl'
    let go [] = DL.empty
        go (L src e : rest)
            | dst `isSubspanOf` src = DL.fromList decs <> DL.fromList rest
            | otherwise = DL.singleton (L src e) <> go rest
    modifyDeclsT (pure . DL.toList . go) a

graftSmallestDeclsWithM ::
    forall a.
    (HasDecls a) =>
    SrcSpan ->
    (LHsDecl GhcPs -> TransformT (Either String) (Maybe [LHsDecl GhcPs])) ->
    Graft (Either String) a
graftSmallestDeclsWithM dst toDecls = Graft $ \dflags a -> do
    let go [] = pure DL.empty
        go (e@(L src _) : rest)
            | dst `isSubspanOf` src = toDecls e >>= \case
                Just decs0 -> do
                    decs <- forM decs0 $ \decl -> do
                        (anns, decl') <-
                            annotateDecl dflags decl
                        modifyAnnsT $ mappend anns
                        pure decl'
                    pure $ DL.fromList decs <> DL.fromList rest
                Nothing -> (DL.singleton e <>) <$> go rest
            | otherwise = (DL.singleton e <>) <$> go rest
    modifyDeclsT (fmap DL.toList . go) a

graftDeclsWithM ::
    forall a m.
    (HasDecls a, Fail.MonadFail m) =>
    SrcSpan ->
    (LHsDecl GhcPs -> TransformT m (Maybe [LHsDecl GhcPs])) ->
    Graft m a
graftDeclsWithM dst toDecls = Graft $ \dflags a -> do
    let go [] = pure DL.empty
        go (e@(L src _) : rest)
            | src == dst = toDecls e >>= \case
                Just decs0 -> do
                    decs <- forM decs0 $ \decl -> do
                        (anns, decl') <-
                            hoistTransform (either Fail.fail pure) $
                            annotateDecl dflags decl
                        modifyAnnsT $ mappend anns
                        pure decl'
                    pure $ DL.fromList decs <> DL.fromList rest
                Nothing -> (DL.singleton e <>) <$> go rest
            | otherwise = (DL.singleton e <>) <$> go rest
    modifyDeclsT (fmap DL.toList . go) a


everywhereM' :: forall m. Monad m => GenericM m -> GenericM m
everywhereM' f = go
    where
        go :: GenericM m
        go = gmapM go <=< f

class (Data ast, Outputable ast) => ASTElement ast where
    parseAST :: Parser (Located ast)
    maybeParensAST :: Located ast -> Located ast

instance p ~ GhcPs => ASTElement (HsExpr p) where
    parseAST = parseExpr
    maybeParensAST = parenthesize

instance p ~ GhcPs => ASTElement (Pat p) where
#if __GLASGOW_HASKELL__ == 808
    parseAST = fmap (fmap $ right $ second dL) . parsePattern
    maybeParensAST = dL . parenthesizePat appPrec . unLoc
#else
    parseAST = parsePattern
    maybeParensAST = parenthesizePat appPrec
#endif

instance p ~ GhcPs => ASTElement (HsType p) where
    parseAST = parseType
    maybeParensAST = parenthesizeHsType appPrec

instance p ~ GhcPs => ASTElement (HsDecl p) where
    parseAST = parseDecl
    maybeParensAST = id

instance p ~ GhcPs => ASTElement (ImportDecl p) where
    parseAST = parseImport
    maybeParensAST = id

instance ASTElement RdrName where
    parseAST df fp = parseWith df fp parseIdentifier
    maybeParensAST = id

------------------------------------------------------------------------------

-- | Dark magic I stole from retrie. No idea what it does.
fixAnns :: ParsedModule -> Annotated ParsedSource
fixAnns ParsedModule {..} =
    let ranns = relativiseApiAnns pm_parsed_source pm_annotations
     in unsafeMkA pm_parsed_source ranns 0

------------------------------------------------------------------------------

-- | Given an 'LHSExpr', compute its exactprint annotations.
--   Note that this function will throw away any existing annotations (and format)
annotate :: ASTElement ast => DynFlags -> Located ast -> TransformT (Either String) (Anns, Located ast)
annotate dflags ast = do
    uniq <- show <$> uniqueSrcSpanT
    let rendered = render dflags ast
    (anns, expr') <- lift $ mapLeft show $ parseAST dflags uniq rendered
    let anns' = setPrecedingLines expr' 0 1 anns
    pure (anns', expr')

-- | Given an 'LHsDecl', compute its exactprint annotations.
annotateDecl :: DynFlags -> LHsDecl GhcPs -> TransformT (Either String) (Anns, LHsDecl GhcPs)
annotateDecl dflags ast = do
    uniq <- show <$> uniqueSrcSpanT
    let rendered = render dflags ast
    (anns, expr') <- lift $ mapLeft show $ parseDecls dflags uniq rendered
    let anns' = setPrecedingLines expr' 1 0 anns
    pure (anns', expr')
------------------------------------------------------------------------------

-- | Print out something 'Outputable'.
render :: Outputable a => DynFlags -> a -> String
render dflags = showSDoc dflags . ppr

------------------------------------------------------------------------------

-- | Put parentheses around an expression if required.
parenthesize :: LHsExpr GhcPs -> LHsExpr GhcPs
parenthesize = parenthesizeHsExpr appPrec
