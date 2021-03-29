{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Rewrite.Test.STLC where

import Rewrite hiding (proof2)
import Data.Foldable
import Control.Monad.State.Strict
import GHC.Exts
import Control.Applicative
import GHC.Generics (Generic)
import Debug.Trace (traceM)
import Data.Functor.Identity (Identity (runIdentity))

testJdg :: Judgement
testJdg = [("a1", "a"), ("bee", "b"), ("c", "c")] :- ("a" :-> "b" :-> TPair "a" "b")


instance MonadExtract Term (State Int) where
  hole = do
    modify (+1)
    pure $ Hole

instance MonadExtract Term Identity where
  hole = pure $ Hole

instance MonadExtract Term IO where
  hole = do
    putStrLn "making a hole"
    pure $ Hole

test :: [Either String (Proof Judgement Int Term)]
test = runIdentity $ runTacticT (0 :: Int) testJdg $ do
  commit lam $ pure ()
  commit lam $ pure ()
  commit lam $ pure ()
  commit lam $ pure ()
  commit lam $ pure ()
  commit lam $ pure ()
  pair

lam :: Functor m => TacticT Judgement Term String s m ()
lam = rule $ \jdg ->
  case jdg of
    hy :- (t :-> a) -> do
      let name = "x"
      ext <- subgoal $ (("x", t) : hy) :- a
      pure $ Lam name ext
    _ -> ThrowR "not a lambda"



-- Just a very simple version of Simply Typed Lambda Calculus,
-- augmented with 'Hole' so that we can have
-- incomplete extracts.
data Term
  = Var String
  | Hole
  | Lam String Term
  | Pair Term Term
  deriving stock (Show, Eq, Generic, Ord)

instance Semigroup Term where
  a <> _ = a

instance Monoid Term where
  mempty = Hole


-- The type part of simply typed lambda calculus
data Type
  = TVar String
  | Type :-> Type
  | TPair Type Type
  deriving stock (Show, Eq, Generic, Ord)

infixr 4 :->

instance IsString Type where
    fromString = TVar


-- A judgement is just a context, along with a goal
data Judgement = [(String, Type)] :- Type
  deriving stock (Show, Eq, Generic, Ord)

auto :: Functor m => TacticT Judgement Term String s m ()
auto = do
  commit pair assumption
  auto

assumption :: Functor m => TacticT Judgement Term String s m ()
assumption = do
  hy :- g <- goal
  case find ((== g) . snd) hy of
    Just v -> rule' $ pure $ Var $ fst v
    Nothing -> throw $ "nothing in scope for " <> show g

pair :: Functor m => TacticT Judgement Term String s m ()
pair = do
  goal >>= \case
    hy :- TPair ta tb -> rule' $ do
      exta <- subgoal $ hy :- ta
      extb <- subgoal $ hy :- tb
      pure $ Pair exta extb
    _ -> throw "not a pair"

instance Semigroup Judgement where
  (<>) = error "no semigroup"

instance Monoid Judgement where
  mempty = [] :- TVar ""

