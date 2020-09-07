{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module Ide.TacticMachinery where

import Control.Arrow
import Data.Char
import Data.Function
import Data.List
import DataCon
import GHC
import GHC.Generics
import GHC.SourceGen.Overloaded
import Name
import Refinery.Tactic
import TcType
import Type


------------------------------------------------------------------------------
-- | A wrapper around 'Type' which supports equality and ordering.
newtype CType = CType { unCType :: Type }

instance Eq CType where
  (==) = eqType `on` unCType

instance Ord CType where
  compare = nonDetCmpType `on` unCType


------------------------------------------------------------------------------
-- | The current bindings and goal for a hole to be filled by refinery.
data Judgement = Judgement
  { jHypothesis :: [(OccName, CType)]
  , jGoal       :: CType
  }
  deriving (Eq, Ord, Generic)


------------------------------------------------------------------------------
-- | Reasons a tactic might fail.
data TacticError
  = UndefinedHypothesis OccName
  | GoalMismatch String CType
  | UnsolvedSubgoals [Judgement]


type ProvableM = ProvableT Judgement (Either TacticError)
type TacticsM = TacticT Judgement (LHsExpr GhcPs) ProvableM
type RuleM    = RuleT Judgement (LHsExpr GhcPs) ProvableM
type Rule     = RuleM (LHsExpr GhcPs)


------------------------------------------------------------------------------
-- | Produce a subgoal that must be solved before we can solve the original
-- goal.
newSubgoal
    :: [(OccName, CType)]  -- ^ Available bindings
    -> CType               -- ^ Sub-goal type
    -> RuleM (LHsExpr GhcPs)
newSubgoal hy g = subgoal =<< newJudgement hy g


------------------------------------------------------------------------------
-- | Create a new judgment
newJudgement
    ::  Monad m
    => [(OccName, CType)]  -- ^ Available bindings
    -> CType               -- ^ Sub-goal type
    -> m Judgement
newJudgement hy g = do
  pure $ Judgement hy g


------------------------------------------------------------------------------
-- | Produce a unique, good name for a type.
mkGoodName
    :: [OccName]  -- ^ Bindings in scope; used to ensure we don't shadow anything
    -> Type       -- ^ The type to produce a name for
    -> OccName
mkGoodName in_scope t =
  let tn = mkTyName t
   in mkVarOcc $ case elem (mkVarOcc tn) in_scope of
        True -> tn ++ show (length in_scope)
        False -> tn


------------------------------------------------------------------------------
-- | Use type information to create a reasonable name.
mkTyName :: Type -> String
-- eg. mkTyName (a -> B) = "fab"
mkTyName (tcSplitFunTys -> ([a@(isFunTy -> False)], b))
  = "f" ++ mkTyName a ++ mkTyName b
-- eg. mkTyName (a -> b -> C) = "f_C"
mkTyName (tcSplitFunTys -> ((_:_), b))
  = "f_" ++ mkTyName b
-- eg. mkTyName (Either A B) = "eab"
mkTyName (splitTyConApp_maybe -> Just (c, args))
  = mkTyConName c ++ foldMap mkTyName args
-- eg. mkTyName a = "a"
mkTyName (getTyVar_maybe-> Just tv)
  = occNameString $ occName tv
-- eg. mkTyName (forall x. y) = "y"
mkTyName (tcSplitSigmaTy-> ((_:_), _, t))
  = mkTyName t
mkTyName _ = "x"


------------------------------------------------------------------------------
-- | Get a good name for a type constructor.
mkTyConName :: TyCon -> String
mkTyConName = fmap toLower . take 1 . occNameString . getOccName


------------------------------------------------------------------------------
-- | Attempt to generate a term of the right type using in-scope bindings, and
-- a given tactic.
runTactic
    :: Type               -- ^ Desired type
    -> [(OccName, Type)]  -- ^ In-scope bindings
    -> TacticsM ()        -- ^ Tactic to use
    -> Either TacticError (LHsExpr GhcPs)
runTactic ty hy t
  = fmap fst
  . runProvableT
  . runTacticT t
  . Judgement (fmap (second CType) hy)
  $ CType ty


instance MonadExtract (LHsExpr GhcPs) ProvableM where
  hole = pure $ noLoc $ HsUnboundVar NoExt $ TrueExprHole $ mkVarOcc "_"


------------------------------------------------------------------------------
-- | Which names are in scope?
getInScope :: [(OccName, a)] -> [OccName]
getInScope = fmap fst


------------------------------------------------------------------------------
-- | Construct a data con with subgoals for each field.
buildDataCon
    :: [(OccName, CType)]  -- ^ In-scope bindings
    -> DataCon             -- ^ The data con to build
    -> [Type]              -- ^ Type arguments for the data con
    -> RuleM (LHsExpr GhcPs)
buildDataCon hy dc apps = do
  let args = dataConInstArgTys dc apps
  sgs <- traverse (newSubgoal hy . CType) args
  pure
    . noLoc
    . foldl' (@@)
        (HsVar NoExt $ noLoc $ Unqual $ nameOccName $ dataConName dc)
    $ fmap unLoc sgs
