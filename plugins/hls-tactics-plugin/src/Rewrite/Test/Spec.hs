{-# LANGUAGE BangPatterns                 #-}
{-# LANGUAGE OverloadedStrings            #-}
{-# OPTIONS_GHC -Wno-deferred-type-errors #-}

module Rewrite.Test.Spec where

import GHC.Generics
import Control.Applicative
import Control.Monad.State.Strict
import Data.Foldable
import Rewrite
import Rewrite.Test.Instances ()
import Rewrite.Test.STLC
import Test.Hspec
import Test.Hspec.QuickCheck (prop, modifyMaxSuccess, modifyMaxSize)
import Test.QuickCheck hiding (Result)
import Test.QuickCheck.Checkers
import Test.QuickCheck.Classes
import Data.Functor.Identity
import Debug.RecoverRTTI (anythingToString)
import Debug.Trace (trace, traceM)
import Data.Monoid
import Control.DeepSeq (force)



type ProofStateTest = ProofState Term String (Int) (State Int)
type TacticTest = TacticT Judgement Term String (Int) (State Int)
type RuleTest = RuleT Judgement Term String (Int) (State Int)

instance Semigroup Int where
  (<>) = (+)

instance Monoid Int where
  mempty = 0


type NoEffects = TacticT Judgement Term String Int Identity

type PS = ProofState Term String [Bool] (State Int) ()


spec :: Spec
spec = modifyMaxSuccess (const 100) $ do

  prop "peek distributes" $ \(t1 :: TT) t2 f ->
    within (1e5) $
      (peek f >> t1 <|> t2) =-= ((peek f >> t1) <|> (peek f >> t2))

  prop "<@> of repeat is bind" $ \(t1 :: TT) (tt :: TT) ->
    within (1e5) $
      t1 <@> repeat tt =-= (t1 >> tt)

  prop "pruning t (const . Just) is t >> throw" $ \(t :: NoEffects ()) e ->
    (pruning t (const $ Just e)) =-= (t >> throw e)

  prop "pruning (const Nothing) is id" $ \(t :: TT) ->
    pruning t (const Nothing) =-= t

  prop "<@> of [] is id" $ \(t1 :: TT) ->
    within (1e5) $
      t1 <@> [] =-= t1

  prop "distrib of tactic" $ \(t1 :: TT) (t2 :: TT) (t3 :: TT) ->
    within (1e5) $
      (t1 >> (t2 >> t3)) =-= ((t1 >> t2) >> t3)

  prop "pull effects out of the left side" $ \(t1 :: TT) (t2 :: TT) e ->
    within (1e5) $
      commit (lift e >> t1) t2 =-= ((lift e :: TT) >> commit t1 t2)

  prop "left distrib put commit" $ \s (t1 :: TT) (t2 :: TT) ->
    within (1e5) $
      (put s >> commit t1 t2) =-= commit (put s >> t1) (put s >> t2)

  prop "right distrib put commit" $ \s (t1 :: TT) (t2 :: TT) ->
    within (1e5) $
      (commit t1 t2 >> put s) =-= commit (t1 >> put s) (t2 >> put s)

  prop "commit x empty is x" $ \(t :: TT) ->
    within (1e5) $
      commit t empty =-= t

  prop "left distrib of <|> over >>=" $ \(t1 :: TI) t2 (t3 :: Int -> TT) ->
    within (1e5) $
      ((t1 <|> t2) >>= t3)
        =-= ((t1 >>= t3) <|> (t2 >>= t3))

  prop "put distrib over alt" $ \(t1 :: TT) t2 s ->
    within (1e5) $
      (put s >> (t1 <|> t2))
        =-= ((put s >> t1) <|> (put s >> t2))

  prop "alt rolls back state" $ \(t :: TT) s ->
    within (1e5) $
      ((put s >> empty) <|> t)
        =-= t

  prop "catch of throw is just the handler" $ \err f ->
    within (1e5) $
      (catch (throw err) f :: TT)
        =-= f err

  prop "catch with rethrowing is id" $ \(t :: TT) ->
    within (1e5) $
      catch t throw
        =-= t

  prop "state is persistent across throw" $ \s e ->
    within (1e5) $
      catch (put s >> throw e) (const $ get >>= mkResult)
        =-= (put s >> mkResult s)

  prop "state is persistent across rule" $ \s ->
    within (1e5) $
      (put s >> (rule' $ get >>= pure . Var . show))
        =-= (put s >> mkResult s)

  prop "commit rolls back state" $ \(t :: TT) s ->
    within (1e5) $
      ((put s >> empty) `commit` t)
        =-= t

  prop "commit takes handling preference over throw" $ \e f (i :: Int) ->
    within (1e5) $
      (catch (throw e `commit` mkResult i) f)
        =-= mkResult i

  prop "catch distributs across alt" $ \t1 t2 f ->
    within (1e5) $
      (catch (t1 <|> t2) f)
        =-= (catch t1 f <|> catch t2 f :: TT)

  prop "commit a rule always succeeds" $ \r t ->
    within (1e5) $
      ((commit (rule r) t) :: TT)
        =-= rule r

  prop "commit semantics" $ \(t :: TT) (m :: TT) err ->
    within (1e5) $
      ((commit (pure ()) t >> m >> throw err) :: TT)
        =-= (m >> throw err)

  prop "commit of pure" $ \(i :: Int) (t :: TI) ->
    within (1e5) $
      (commit (pure i) t >>= mkResult)
        =-= mkResult i

  prop "commit runs its continuation" $ \(i :: Int) (t :: TI) f ->
    within (1e5) $
      ((commit (pure i) t >> f) :: TT)
        =-= f

  prop "committing a hole keeps state" $ \s (t :: TT) ->
    within (1e5) $
      (commit (put s) t >> get >>= mkResult)
        =-= (put s >> get >>= mkResult)

  prop "effect works properly" $
    expectFailure $ \(e :: State Int ()) (t :: TT) ->
      (lift e >> t) =-= t

  prop "this is the broken commit test" $
    expectFailure $ \(t1 :: TI) t2 (t3 :: Int -> TT) ->
      (commit t1 t2 >>= t3)
        =-= (t1 >>= t3) `commit` (t2 >>= t3)

--   describe "proofstate" $ do
--     testBatch $ functor     (undefined :: ProofStateTest (Int, Int, Int))
--     testBatch $ applicative (undefined :: ProofStateTest (Int, Int, Int))
--     testBatch $ alternative (undefined :: ProofStateTest Int)
--     testBatch $ monad       (undefined :: ProofStateTest (Int, Int, Int))
--     testBatch $ monadPlus   (undefined :: ProofStateTest (Int, Int))
--     testBatch $ monadState  (undefined :: ProofStateTest (Int, Int))

  describe "rule" $ do
    testBatch $ functor     (undefined :: RuleTest (Term, Term, Term))
    testBatch $ applicative (undefined :: RuleTest (Term, Term, Term))
    testBatch $ monad       (undefined :: RuleTest (Term, Term, Term))

  describe "tactic" $ do
    testBatch $ functor     (undefined :: TacticTest ((), (), ()))
    testBatch $ applicative (undefined :: TacticTest ((), (), ()))
    testBatch $ alternative (undefined :: TacticTest ())
    testBatch $ monad       (undefined :: TacticTest ((), (), ()))
    testBatch $ monadPlus   (undefined :: TacticTest ((), ()))
    testBatch $ monadState  (undefined :: TacticTest ((), ()))


testBatch :: TestBatch -> Spec
testBatch (group, tests) =
  describe group $
    for_ tests $ uncurry prop


main :: IO ()
main = do
  hspec spec


mkResult :: Show a => a -> TT
mkResult = rule' . pure . Var . show


type TI = TacticTest Int
type TT = TacticTest ()

monadState
    :: forall m s a b
     . ( MonadState s m
       , EqProp (m s)
       , EqProp (m ())
       , Show s
       , Arbitrary s
       )
    => m (a, b)
    -> TestBatch
monadState _ =
  ( "MonadState laws"
  , [ ("get >> get", (get >> get) =-= get @s @m)
    , ("get >>= put", (get @s @m >>= put) =-= pure ())
    , ("put >> put", property $ do
        s1 <- arbitrary
        s2 <- arbitrary
        pure $
          counterexample (show s1) $
          counterexample (show s2) $
            (put @_ @m s1 >> put s2) =-= put s2
      )
    , ("put >> get", property $ do
        s <- arbitrary
        pure $
          counterexample (show s) $
            (put s >> get) =-= (put s >> pure @m s)
      )
    ]
  )

traceShowAnything :: a -> a
traceShowAnything a = trace (anythingToString a) a

type TIO = TacticT Judgement Term String Int IO

testJdg2 :: Judgement
testJdg2 = [] :- ("a" :-> "b" :-> TPair "a" "b")

test :: IO ()
test = do
  let (x :: NoEffects ()) = do
        peek $ \case
          Lam _ Hole -> throw "incomplete"
          _ -> pure ()
        lam <|> pure ()

  print $ force $
    fmap (fmap proof_extract) $ runIdentity $
      runDebugTacticT 2 testJdg2 x


test2 :: IO ()
test2 = do
  let (x :: TIO ()) = do
        throw "err" >> lift (putStrLn "Oh bother")

  print =<< runTacticT 2 testJdg2 x

