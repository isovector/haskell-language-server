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

testJdg :: Judgement
testJdg = [("a1", "a"), ("bee", "b"), ("c", "c")] :- TPair "a" (TPair "b" "c")


instance Applicative m => MonadExtract Term m where
  hole = pure Hole

proof2 :: Monad m => s -> ProofState Term err s m a -> m [Either err (s, Term)]
proof2 s =
  kill s
    (\s' _ x -> proof2 s' $ x =<< hole)
    (\s -> pure . pure . Right . (s, ))
    (pure [])
    (const $ pure . pure . Left)
    join
    (liftA2 (<>))

runTactic2
    :: Monad m
    => s
    -> Judgement
    -> TacticT Judgement Term err s m a
    -> m [Either err (s, Term)]
runTactic2 s jdg (TacticT m) = proof2 s $ execStateT m jdg



-- Just a very simple version of Simply Typed Lambda Calculus,
-- augmented with 'Hole' so that we can have
-- incomplete extracts.
data Term
  = Var String
  | Hole
  | Lam String Term
  | Pair Term Term
  deriving stock (Show, Eq, Generic, Ord)


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
    Just v -> rule $ pure $ Var $ fst v
    Nothing -> throw $ "nothing in scope for " <> show g

pair :: Functor m => TacticT Judgement Term String s m ()
pair = do
  goal >>= \case
    hy :- TPair ta tb -> rule $ do
      exta <- subgoal $ hy :- ta
      extb <- subgoal $ hy :- tb
      pure $ Pair exta extb
    _ -> throw "not a pair"

instance Semigroup Judgement where
  (<>) = error "no semigroup"

instance Monoid Judgement where
  mempty = [] :- TVar ""

