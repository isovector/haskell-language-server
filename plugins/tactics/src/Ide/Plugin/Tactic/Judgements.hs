{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns     #-}

module Ide.Plugin.Tactic.Judgements where

import Control.Lens hiding (Context)
import           Data.Char
import           Data.Coerce
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe
import qualified Data.Set as S
import           Development.IDE.Spans.LocalBindings
import           Ide.Plugin.Tactic.Types
import           OccName
import           SrcLoc
import           Type
import Data.Generics.Product (field)


------------------------------------------------------------------------------
-- | Given a 'SrcSpan' and a 'Bindings', create a hypothesis.
hypothesisFromBindings :: RealSrcSpan -> Bindings -> Map OccName CType
hypothesisFromBindings span bs = buildHypothesis $ getLocalScope bs span

------------------------------------------------------------------------------
-- | Convert a @Set Id@ into a hypothesis.
buildHypothesis :: [(Name, Maybe Type)] -> Map OccName CType
buildHypothesis
  = M.fromList
  . mapMaybe go
  where
    go (occName -> occ, t)
      | Just ty <- t
      , isAlpha . head . occNameString $ occ = Just (occ, CType ty)
      | otherwise = Nothing


hasDestructed :: Judgement -> OccName -> Bool
hasDestructed j n = S.member n $ _jDestructed j

destructing :: OccName -> Judgement -> Judgement
destructing n = field @"_jDestructed" <>~ S.singleton n

blacklistingDestruct :: Judgement -> Judgement
blacklistingDestruct =
  field @"_jBlacklistDestruct" .~ True

isDestructBlacklisted :: Judgement -> Bool
isDestructBlacklisted = _jBlacklistDestruct

withNewGoal :: a -> Judgement' a -> Judgement' a
withNewGoal t = field @"_jGoal" .~ t

introducing :: [(OccName, a)] -> Judgement' a -> Judgement' a
introducing ns =
  field @"_jHypothesis" <>~ M.fromList ns

withHypothesis
    :: (Map OccName a -> Map OccName a)
    -> Judgement' a
    -> Judgement' a
withHypothesis f =
  field @"_jHypothesis" %~ f

------------------------------------------------------------------------------
-- | Pattern vals are currently tracked in jHypothesis, with an extra piece of data sitting around in jPatternVals.
introducingPat :: [(OccName, a)] -> Judgement' a -> Judgement' a
introducingPat ns jdg = jdg
  & field @"_jHypothesis"  <>~ M.fromList ns
  & field @"_jPatternVals" <>~ S.fromList (fmap fst ns)


disallowing :: [OccName] -> Judgement' a -> Judgement' a
disallowing ns =
  field @"_jHypothesis" %~ flip M.withoutKeys (S.fromList ns)


jHypothesis :: Judgement' a -> Map OccName a
jHypothesis = _jHypothesis


------------------------------------------------------------------------------
-- | Only the hypothesis members which are pattern vals
jPatHypothesis :: Judgement' a -> Map OccName a
jPatHypothesis jdg
  = M.restrictKeys (jHypothesis jdg) $ _jPatternVals jdg


jGoal :: Judgement' a -> a
jGoal = _jGoal


substJdg :: TCvSubst -> Judgement -> Judgement
substJdg subst = fmap $ coerce . substTy subst . coerce

mkFirstJudgement :: M.Map OccName CType -> Type -> Judgement' CType
mkFirstJudgement hy = Judgement hy mempty mempty False mempty mempty . CType

