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

instance Eq (TacticT jdg ext err s m a) where
  (==) = (==) `on` anythingToString

instance Ord (TacticT jdg ext err s m a) where
  compare = compare `on` anythingToString


instance CoArbitrary Judgement where
  coarbitrary (hy :- g) = coarbitrary (hy, g)

instance CoArbitrary Type where
  coarbitrary (TVar l_c) = variant @Int 0 . coarbitrary l_c
  coarbitrary (t :-> t2) = variant @Int 1 . coarbitrary (t, t2)
  coarbitrary (TPair t t2) = variant @Int 2 . coarbitrary (t, t2)

instance CoArbitrary Term where
  coarbitrary (Var l_c) = variant @Int 0 . coarbitrary l_c
  coarbitrary (Hole) = variant @Int 1
  coarbitrary (Lam l_c t) = variant @Int 2 . coarbitrary (l_c, t)
  coarbitrary (Pair t t2) = variant @Int 3 . coarbitrary (t, t2)

instance Arbitrary Term where
  arbitrary
    = let terminal = [Var <$> arbitrary, pure Hole]
      in sized $ \ n -> case n <= 1 of
           True -> oneof terminal
           False -> oneof $
             [ Lam <$> arbitrary <*> scale (subtract 1) arbitrary
             , Pair <$> scale (flip div 2) arbitrary <*> scale (flip div 2) arbitrary
             ] <> terminal


instance ( Arbitrary err
         , CoArbitrary err
         , Arbitrary ext
         , CoArbitrary ext
         , Arbitrary a
         , CoArbitrary s
         , Arbitrary s
         , Arbitrary (m (ProofState ext err s m a))
         , Arbitrary (m (ProofState ext err s m Int))
         ) => Arbitrary (ProofState ext err s m a) where
  arbitrary =
    let terminal = [pure Empty, Throw <$> arbitrary, Axiom <$> arbitrary]
     in sized $ \n -> case n <= 1 of
          True  -> oneof terminal
          False -> oneof $
            [ Subgoal <$> arbitrary <*> scale (subtract 1) arbitrary
            , Effect <$> scale (subtract 1) arbitrary
            , Stateful <$> scale (subtract 1) arbitrary
            , Alt <$> scale (flip div 2) arbitrary
                  <*> scale (flip div 2) arbitrary
            , Commit <$> scale (flip div 3) (arbitrary @(ProofState ext err s m Int))
                     <*> scale (flip div 3) arbitrary
                     <*> scale (flip div 3) arbitrary
            , Handle <$> scale (flip div 3) (arbitrary @(ProofState ext err s m Int))
                     <*> scale (flip div 3) arbitrary
                     <*> scale (flip div 3) arbitrary
            ] <> terminal

instance ( Arbitrary err
         , CoArbitrary err
         , Arbitrary ext
         , CoArbitrary ext
         , Arbitrary a
         , CoArbitrary s
         , Arbitrary s
         , Arbitrary (m (ProofState ext err s m a))
         , Arbitrary (m (ProofState ext err s m Int))
         , Typeable a
         , Functor m
         , Arbitrary jdg
         , Arbitrary (m (Rule jdg ext err s m ext))
         ) => Arbitrary (TacticT jdg ext err s m a) where
  arbitrary = oneof
    [ arb
    , case eqT @a @() of
        Just Refl -> fmap rule arbitrary
        Nothing -> arb
    ]
    where
      arb = TacticT . lift <$> arbitrary

instance  ( Arbitrary a
          , Arbitrary jdg
          , CoArbitrary s
          , Arbitrary s
          , Arbitrary (m (Rule jdg ext err s m a))
          , CoArbitrary ext
          ) => Arbitrary (Rule jdg ext err s m a) where
  arbitrary
    = let terminal = [Pure <$> arbitrary]
      in sized $ \n -> case n <= 1 of
           True  -> oneof terminal
           False -> oneof $
            [ SubgoalR <$> arbitrary <*> scale (flip div 2) arbitrary
            , EffectR <$> scale (flip div 2) arbitrary
            , StatefulR <$> scale (flip div 2) arbitrary
            ] <> terminal

instance (Arbitrary s, EqProp s, EqProp a) => EqProp (State s a) where
  a =-= b = property $ do
    s <- arbitrary
    pure $ runState a s =-= runState b s

instance (CoArbitrary s, Arbitrary a, Arbitrary s) => Arbitrary (State s a) where
  arbitrary = oneof
    [ pure <$> arbitrary
    , (>>) <$> (fmap put arbitrary) <*> scale (flip div 2) arbitrary
    , (>>=) <$> pure get <*> scale (flip div 2) arbitrary
    ]


instance ( Arbitrary s
         , Monad m
         , EqProp (m [Result s jdg err ext])
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
         , Monad m
         , Arbitrary jdg
         , EqProp (m [Result s jdg err Term])
         ) => EqProp (TacticT jdg Term err s m a) where
  a =-= b = property $ do
    s <- arbitrary @s
    jdg <- arbitrary @jdg
    pure $ runTactic s jdg a =-= runTactic s jdg b

instance {-# OVERLAPPING #-}
         ( Arbitrary s
         , Monad m
         , EqProp (m [Either err (s, Term)])
         ) => EqProp (TacticT Judgement Term err s m a) where
  a =-= b = property $ do
    s <- arbitrary @s
    jdg <- arbitrary @Judgement
    pure $ runTactic2 @m s jdg a =-= runTactic2 s jdg b

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

instance (EqProp s, EqProp jdg, EqProp err, EqProp ext) => EqProp (Result s jdg err ext)
instance EqProp Term
instance EqProp Judgement
instance EqProp Type

