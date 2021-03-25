{-# OPTIONS_GHC -Wno-orphans #-}

module Rewrite.Test.QuickSpec where

import Rewrite
import Rewrite.Test.Instances ()
import Control.Monad.State.Strict
import Control.Applicative
import QuickSpec
import Data.Word
import Rewrite.Test.STLC


type S = Word8
type SMS = Maybe Word8
type Err = Bool

type T = TacticT Judgement Term Err S (State SMS)
type Def = Int

instance Observe (S, SMS, Judgement) ([Either Err Term], SMS) (T a) where
  observe (s, sms, jdg) = flip runState sms . runTactic2 s jdg

instance Ord a => Observe SMS (a, SMS) (State SMS a) where
  observe sms = flip runState sms

sig :: Sig
sig = signature
  [ monoObserveVars @(T Def) ["t"]
  , monoObserveVars @(State SMS Def) ["eff"]
  , monoObserveVars @(Err) ["err"]
  , monoObserveVars @(S) ["s"]

  , background
      [ con @(A -> T A) "pure" pure
      , con @(T A -> T B -> T B) ">>" (>>)
      , con @(T Def) "empty" empty
      , con @(T Def -> T Def -> T Def) "<|>" (<|>)
      ]

  , con @(T Def -> T Def -> T Def) "commit" commit
  , con @(Err -> T A) "throw" throw
  , con @(State SMS Def -> T Def) "lift" lift
  , con @(S -> T ()) "put" put

  -- , con @(T Def -> (Err -> T Def) -> T Def) "catch" catch

  -- , withMaxTermSize 9
  , defaultTo $ Proxy @Def
  ]

main :: IO ()
main = quickSpec sig


