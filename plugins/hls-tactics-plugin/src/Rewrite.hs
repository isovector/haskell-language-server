{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Rewrite where

import Control.Monad.State.Strict
import Control.Applicative
import Test.QuickCheck.Classes ()
import GHC.Generics (Generic)
import Data.Tuple (swap)
import Debug.RecoverRTTI


data ProofState ext err s m a where
  Subgoal
    :: a
    -> (ext -> ProofState ext err s m a)
    -> ProofState ext err s m a
  Effect
    :: m (ProofState ext err s m a)
    -> ProofState ext err s m a
  Stateful
    :: (s -> (s, ProofState ext err s m a))
    -> ProofState ext err s m a
  Alt
    :: ProofState ext err s m a
    -> ProofState ext err s m a
    -> ProofState ext err s m a
  Interleave
    :: ProofState ext err s m a
    -> ProofState ext err s m a
    -> ProofState ext err s m a
  Commit
    :: ProofState ext err s m x
    -> ProofState ext err s m x
    -> (x -> ProofState ext err s m a)
    -> ProofState ext err s m a
  Empty
    :: ProofState ext err s m a
  Handle
    :: ProofState ext err s m x
    -> (err -> ProofState ext err s m x)
    -> (x -> ProofState ext err s m a)
    -> ProofState ext err s m a
  Throw
    :: err
    -> ProofState ext err s m a
  Axiom
    :: ext
    -> ProofState ext err s m a

newtype TacticT jdg ext err s m a = TacticT
  { unTacticT :: StateT jdg (ProofState ext err s m) a
  } deriving newtype (Functor, Applicative, Monad, Alternative, MonadPlus)

instance MonadTrans (Rule jdg ext err s) where
  lift ma = EffectR $ fmap pure ma

instance MonadTrans (ProofState ext err s) where
  lift ma = Effect $ fmap pure ma

instance MonadTrans (TacticT jdg ext err s) where
  lift ma = TacticT $ StateT $ \jdg -> fmap (, jdg) $ Effect $ fmap pure ma

data Rule jdg ext err s m a where
  Pure
    :: a
    -> Rule jdg ext err s m a
  SubgoalR
    :: jdg
    -> (ext -> Rule jdg ext err s m a)
    -> Rule jdg ext err s m a
  EffectR
    :: m (Rule jdg ext err s m a)
    -> Rule jdg ext err s m a
  StatefulR
    :: (s -> (s, Rule jdg ext err s m a))
    -> Rule jdg ext err s m a
  deriving stock (Functor)

instance Show (ProofState ext err s m a) where
  show = anythingToString

instance (Show ext, Show err, Show jdg, Monoid jdg, Show a) =>
    Show (TacticT jdg ext err s m a) where
  show (TacticT t) = show $ runStateT t mempty


instance Functor m => Functor (ProofState ext err s m) where
  fmap f (Subgoal a k)
    = Subgoal (f a) $ fmap f . k
  fmap f (Effect m)
    = Effect $ fmap (fmap f) m
  fmap f (Stateful m)
    = Stateful $ fmap (fmap (fmap f)) m
  fmap f (Alt t1 t2)
    = Alt (fmap f t1) (fmap f t2)
  fmap f (Interleave t1 t2)
    = Interleave (fmap f t1) (fmap f t2)
  fmap f (Commit t1 t2 k)
    = Commit t1 t2 $ fmap f . k
  fmap _ Empty
    = Empty
  fmap _ (Throw err)
    = Throw err
  fmap f (Handle t1 h k)
    = Handle t1 h $ fmap f . k
  fmap _ (Axiom ext)
    = Axiom ext

instance Functor m => Applicative (ProofState ext err s m) where
  pure a = Subgoal a Axiom
  (<*>) = ap

instance Functor m => Monad (ProofState ext err s m) where
  return = pure
  (>>=) (Subgoal a k) f = applyCont (f <=< k) $ f a
  (>>=) (Effect m) f = Effect $ fmap (f =<<) m
  (>>=) (Stateful m) f = Stateful $ fmap (fmap (f =<<)) m
  (>>=) (Alt t1 t2) f = Alt (t1 >>= f) (t2 >>= f)
  (>>=) (Interleave t1 t2) f = Interleave (f =<< t1) (f =<< t2)
  (>>=) (Commit t1 t2 k) f = Commit t1 t2 $ f <=< k
  (>>=) Empty _ = Empty
  (>>=) (Handle t h k) f = Handle t h $ f <=< k
  (>>=) (Throw err) _ = Throw err
  (>>=) (Axiom ext) _ = Axiom ext

instance Functor m => MonadState s (ProofState ext err s m) where
  state s = Stateful $ fmap (fmap pure . swap) s

instance Functor m => Alternative (ProofState ext err s m) where
  empty = Empty
  (<|>) = Alt

instance Functor m => MonadPlus (ProofState ext err s m) where
  mzero = empty
  mplus = (<|>)


applyCont
    :: (Functor m)
    => (ext -> ProofState ext err s m a)
    -> ProofState ext err s m a
    -> ProofState ext err s m a
applyCont k (Subgoal goal k')
  = Subgoal goal (applyCont k . k')
applyCont k (Effect m)
  = Effect (fmap (applyCont k) m)
applyCont k (Stateful s)
  = Stateful $ fmap (applyCont k) . s
applyCont k (Alt p1 p2)
  = Alt (applyCont k p1) (applyCont k p2)
applyCont k (Interleave p1 p2)
  = Interleave (applyCont k p1) (applyCont k p2)
applyCont k (Commit p1 p2 k')
  = Commit p1 p2 $ applyCont k . k'
applyCont k (Handle t h k')
  = Handle t h $ applyCont k . k'
applyCont _ Empty
  = Empty
applyCont _ (Throw err)
  = Throw err
applyCont k (Axiom ext)
  = k ext


instance Functor m => MonadState s (TacticT jdg ext err s m) where
  state s = TacticT $ lift $ Stateful $ fmap (fmap pure . swap) s


deriving instance (Show a, Show jdg, Show (m (Rule jdg ext err s m a))) =>
  Show (Rule jdg ext err s m a)

instance Functor m => MonadState s (Rule jdg ext err s m) where
  state s =  StatefulR $ fmap (fmap pure . swap) s


instance Functor m => Applicative (Rule jdg ext err s m) where
  pure a = Pure a
  (<*>) = ap


instance Functor m => Monad (Rule jdg ext err s m) where
  return = pure
  (>>=) (Pure a) f = f a
  (>>=) (SubgoalR jdg k) f = SubgoalR jdg $ f <=< k
  (>>=) (EffectR m) f = EffectR $ fmap (f =<<) m
  (>>=) (StatefulR m) f = StatefulR $ fmap (fmap (f =<<)) m


rule
    :: Functor m
    => Rule jdg ext err s m ext
    -> TacticT jdg ext err s m ()
rule r = TacticT $ StateT $ const $ fmap ((), ) $ ruleToProof r


ruleToProof
    :: Functor m
    => Rule jdg ext err s m ext
    -> ProofState ext err s m jdg
ruleToProof (Pure ext)
  = Axiom ext
ruleToProof (SubgoalR jdg k)
  = Subgoal jdg $ ruleToProof . k
ruleToProof (EffectR m)
  = Effect $ fmap ruleToProof m
ruleToProof (StatefulR m)
  = Stateful $ fmap (fmap ruleToProof) m


goal :: Functor m => TacticT jdg ext err s m jdg
goal = TacticT get


subgoal :: Functor m => jdg -> Rule jdg ext err s m ext
subgoal jdg = SubgoalR jdg pure


throw :: Functor m => err -> TacticT jdg ext err s m a
throw = TacticT . lift . Throw



class MonadExtract ext m | m -> ext where
  hole :: m ext


kill
    :: (Monad m, MonadExtract ext m)
    => s
    -> (s -> a -> (ext -> ProofState ext err s m a) -> m r)
    -> (ext -> m r)
    -> m r
    -> (s -> err -> m r)
    -> (m (m r) -> m r)
    -> (m r -> m r -> m r)
    -> ProofState ext err s m a
    -> m r
kill s sub _ _ _ _ _ (Subgoal a k) = do
  sub s a k

kill s sub ok cut raise eff keep (Effect m) = do
  eff $ fmap (kill s sub ok cut raise eff keep) m

kill s sub ok cut raise eff keep (Stateful m) =
  let (s', t) = m s
   in kill s' sub ok cut raise eff keep t

kill s sub ok cut raise eff keep (Alt t1 t2) =
  keep (kill s sub ok cut raise eff keep t1)
       (kill s sub ok cut raise eff keep t2)

kill s sub ok cut raise eff keep (Interleave t1 t2) =
  -- TODO(sandy): for now
  keep (kill s sub ok cut raise eff keep t1)
       (kill s sub ok cut raise eff keep t2)

kill s sub ok cut raise eff keep (Commit (t1 :: ProofState ext err s m x) t2 k) = do
  let kill_as_proofstate t =
        kill s
          (\s' a k' -> pure $ put s' >> Subgoal a k')
          (pure . Axiom)
          (pure Empty)
          (\s' err -> pure $ put s' >> Throw err)
          (pure . Effect . join)
          (liftA2 (<|>))
          t
  (x1 :: ProofState ext err s m x) <-
    kill_as_proofstate t1
  let run_t2 sub' ok' cut' raise eff' keep' = do
        (x2 :: ProofState ext err s m x) <-
          kill_as_proofstate t2
        kill s sub' ok' cut' raise eff' keep' $ k =<< x2

      sub' = (\s' x k' -> kill s' sub ok cut raise eff keep $ Subgoal x k' >>= k)

  kill s sub' ok
               (run_t2 sub ok cut            raise eff keep)
    (\s' err -> run_t2 sub ok (raise s' err) raise eff keep)
    eff keep x1

kill _ _ _ cut _ _ _ Empty = cut

kill s sub ok cut raise eff keep (Handle t h k)
  = let sub' = \s' x k' -> kill s' sub ok cut raise eff keep $ Subgoal x k' >>= k
     in kill s sub' ok cut
          (\s' err -> kill s' sub' ok cut raise eff keep $ h err) eff keep t

kill s _ _ _ raise _ _ (Throw err) = raise s err

kill _ _ ok _ _ _ _ (Axiom ext) = ok ext


data Result jdg err ext
  = HoleResult jdg
  | ErrorResult err
  | Extract ext
  | NoResult
  deriving stock (Show, Generic)


proof :: (MonadExtract ext m , Monad m) => s -> ProofState ext err s m jdg -> m [Result jdg err ext]
proof s =
  kill s
    ( \s' _ x -> proof s' $ x =<< lift hole)
    (pure . pure . Extract)
    (pure [])
    (const $ pure . pure . ErrorResult)
    join
    (liftA2 (<>))


runTactic :: (MonadExtract ext m, Monad m) => s -> jdg -> TacticT jdg ext err s m a -> m [Result jdg err ext]
runTactic s jdg (TacticT m) = proof s $ execStateT m jdg


commit :: Functor m => TacticT jdg ext err s m a -> TacticT jdg ext err s m a -> TacticT jdg ext err s m a
commit (TacticT t1) (TacticT t2) = TacticT $ StateT $ \jdg ->
  Commit (runStateT t1 jdg) (runStateT t2 jdg) pure


catch
    :: Functor m
    => TacticT jdg ext err s m a
    -> (err -> TacticT jdg ext err s m a)
    -> TacticT jdg ext err s m a
catch (TacticT t) h = TacticT $ StateT $ \jdg ->
  Handle
    (runStateT t jdg)
    (flip runStateT jdg . unTacticT . h)
    pure

