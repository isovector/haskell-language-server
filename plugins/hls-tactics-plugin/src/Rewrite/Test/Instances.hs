{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UndecidableInstances               #-}
{-# OPTIONS_GHC -fno-warn-orphans               #-}

module Rewrite.Test.Instances where

import Rewrite
import Rewrite.Test.STLC
import Control.Monad.State.Strict
import Test.QuickCheck hiding (Result)
import Test.QuickCheck.Checkers
import Data.Functor.Identity
import Data.Data (Typeable, eqT, (:~:) (Refl))
import Debug.RecoverRTTI (anythingToString)
import Data.Function (on)
import Debug.Trace (traceM)
import Control.Applicative ((<|>), Alternative (empty))

instance (MonadExtract ext m, Monoid jdg, Monoid s, Ord (m [Result s err ext]))
  => Eq (TacticT jdg ext err s m a) where
  a == b  = compare a b == EQ

instance (MonadExtract ext m, Monoid jdg, Monoid s, Ord (m [Result s err ext])) => Ord (TacticT jdg ext err s m a) where
  compare = do
    compare `on` runTactic mempty mempty

instance CoArbitrary Judgement where
  coarbitrary (hy :- g) = coarbitrary (hy, g)

instance CoArbitrary Type where
  coarbitrary (TVar l_c) = variant @Int 0 . coarbitrary l_c
  coarbitrary (t :-> t2) = variant @Int 1 . coarbitrary (t, t2)
  coarbitrary (TPair t t2) = variant @Int 2 . coarbitrary (t, t2)

instance CoArbitrary Term where
  coarbitrary (Var l_c) = variant @Int 0 . coarbitrary l_c
  coarbitrary (Hole ) = variant @Int 1
  coarbitrary (Lam l_c t) = variant @Int 2 . coarbitrary (l_c, t)
  coarbitrary (Pair t t2) = variant @Int 3 . coarbitrary (t, t2)

instance Arbitrary Term where
  arbitrary
    = let terminal = [Var <$> arbitrary, pure Hole]
      in sized $ \ n -> case n <= 1 of
           True -> oneof terminal
           False -> oneof $
             [ Lam <$> arbitrary <*> scale (flip div 2) arbitrary
             , Pair <$> scale (flip div 2) arbitrary <*> scale (flip div 2) arbitrary
             ] <> terminal


instance ( Arbitrary err
         , CoArbitrary err
         , Arbitrary ext
         , CoArbitrary ext
         , Arbitrary a
         , CoArbitrary s
         , Arbitrary s
         , Typeable a
         , Typeable ext
         , Monad m
         , Arbitrary jdg
         , CoArbitrary jdg
         , Arbitrary (m (Rule jdg ext err s m ext))
         , Arbitrary (m (Rule jdg ext err s m Int))
         , Arbitrary (m Int)
         , Arbitrary (m ext)
         ) => Arbitrary (TacticT jdg ext err s m a) where
  arbitrary = oneof
    [ arb
    -- , case eqT @a @() of
    --     Just Refl -> fmap rule arbitrary
    --     Nothing -> arb
    ]
    where
      arb = oneof
        [
          -- commit <$> scale (flip div 2) arbitrary
          --        <*> scale (flip div 2) arbitrary
          throw <$> arbitrary
        , (<|>) <$> scale (flip div 2) arbitrary
                <*> scale (flip div 2) arbitrary
        , pure empty
        , catch <$> scale (flip div 2) arbitrary
                <*> scale (flip div 2) arbitrary
        , (>>) <$> (arbitrary @(TacticT jdg ext err s m Int))
               <*> scale (flip div 2) arbitrary
        , pure <$> arbitrary
        , case eqT @a @() of
            Just Refl -> fmap rule arbitrary
            Nothing -> pure <$> arbitrary
        ]

instance  ( Arbitrary a
          , Arbitrary jdg
          , CoArbitrary s
          , Arbitrary s
          , Arbitrary (m (Rule jdg ext err s m a))
          , Arbitrary (m (Rule jdg ext err s m Int))
          , Arbitrary (m (Rule jdg ext err s m ext))
          , CoArbitrary ext
          , Typeable a
          , Typeable ext
          , Monad m
          , Arbitrary ext
          , Arbitrary (m a)
          , Arbitrary (m ext)
          , Arbitrary (m Int)
          ) => Arbitrary (Rule jdg ext err s m a) where
  arbitrary
    = let terminal = [pure <$> arbitrary]
      in sized $ \n -> case n <= 1 of
           True  -> oneof terminal
           False -> oneof $
            [
              case eqT @a @ext of
                Just Refl -> subgoal <$> arbitrary
                Nothing -> pure <$> arbitrary
            , (>>) <$> (arbitrary @(Rule jdg ext err s m ext))
                   <*> scale (flip div 2) arbitrary
            , lift <$> scale (flip div 2) arbitrary
            , StatefulR <$> scale (flip div 2) arbitrary
            ] <> terminal

instance (EqProp a, EqProp s, Eq a, Eq s, Show s, Show a, Arbitrary s) => EqProp (State s a) where
  a =-= b = property $ do
    s <- arbitrary
    let sa = runState a s
        sb = runState b s
    -- pure $ counterexample (show sa) $
    --   counterexample (show sb) $
    pure $ sa =-= sb

instance (CoArbitrary s, Arbitrary a, Arbitrary s) => Arbitrary (State s a) where
  arbitrary = oneof
    [ pure <$> arbitrary
    , (>>) <$> (fmap put arbitrary) <*> scale (flip div 2) arbitrary
    , (>>=) <$> pure get <*> scale (flip div 2) arbitrary
    ]


instance ( Arbitrary s
         , EqProp (m [Result s err ext])
         , MonadExtract ext m
         ) => EqProp (ProofState ext err s m jdg) where
  a =-= b = property $ do
    s <- arbitrary @s
    pure $ proof s a =-= proof s b

instance ( Monad m
         , EqProp (TacticT jdg ext err s m ())
         ) => EqProp (Rule jdg ext err s m ext) where
  a =-= b = rule a =-= rule b

instance ( Arbitrary s
         , Arbitrary jdg
         , EqProp (m [Result s err ext])
         , Show (m [Result s err ext])
         , MonadExtract ext m
         ) => EqProp (TacticT jdg ext err s m a) where
  a =-= b = property $ do
    s <- arbitrary @s
    jdg <- arbitrary @jdg
    let ma = runTactic s jdg a
        mb = runTactic s jdg b
    pure $
      counterexample (show ma) $
        counterexample (show mb) $
          ma =-= mb

instance {-# OVERLAPPING #-}
         ( Arbitrary s
         , Monad m
         , EqProp (m [Either err (s, Term)])
         , Show (m [Either err (s, Term)])
         , m ~ State Int
         ) => EqProp (TacticT Judgement Term err s m a) where
  a =-= b = property $ do
    s <- arbitrary @s
    jdg <- arbitrary @Judgement
    let ma = runTactic2 s jdg a
        mb = runTactic2 s jdg b
    pure $
      counterexample (show ma) $
        counterexample (show mb) $
          ma =-= mb


instance Arbitrary Type where
  arbitrary
    = let terminal = [TVar <$> arbitrary]
      in sized $ \ n ->
        case n <= 1 of
          True  -> oneof terminal
          False -> oneof $
            [ (:->) <$> scale (flip div 2) arbitrary
                    <*> scale (flip div 2) arbitrary
            , TPair <$> scale (flip div 2) arbitrary
                    <*> scale (flip div 2) arbitrary
            ] <> terminal

instance Show a => Show (StateT Int Identity a) where
  show = show . flip runState 999

instance Arbitrary Judgement where
  arbitrary = (:-) <$> scale (flip div 3) arbitrary <*> scale (flip div 2) arbitrary

instance (Eq err, Show err, Eq ext, Show ext, Eq s, Show s) => EqProp (Result s err ext) where
  (=-=) a b = property $
    counterexample (show a) $
    counterexample (show b) $
      a === b

instance EqProp Term
instance EqProp Judgement
instance EqProp Type

