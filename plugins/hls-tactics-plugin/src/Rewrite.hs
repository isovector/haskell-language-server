{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE RankNTypes #-}

module Rewrite where

import Control.Monad.State.Strict
import Control.Applicative
import Test.QuickCheck.Classes ()
import GHC.Generics (Generic)
import Data.Tuple (swap)
import Debug.RecoverRTTI
import Debug.Trace (traceM)


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



class Monad m => MonadExtract ext m | m -> ext where
  hole :: m ext


data Blah ext err s m a = Blah
  { unBlah
      :: forall r
       . s
      -> (s -> a -> (ext -> Blah ext err s m a) -> r)
      -> (forall x. s -> Blah ext err s m x -> Blah ext err s m x -> (x -> Blah ext err s m a) -> r)
      -> (s -> ext -> r)
      -> r
      -> (s -> err -> r)
      -> (m r -> r)
      -> (r -> r -> r)
      -> r
  }

instance Alternative (Blah ext err s m) where
  Blah m1 <|> Blah m2 = Blah $ \s sub comm ok cut raise eff keep ->
    keep (m1 s sub comm ok cut raise eff keep) (m2 s sub comm ok cut raise eff keep)
  empty = Blah $ \_ _ _ _ cut _ _ _ -> cut

instance MonadPlus (Blah ext err s m) where

instance MonadTrans (Blah ext err s) where
  lift ma = Blah $ \s sub comm ok cut raise eff keep -> eff $
    fmap (\a -> unBlah (pure a) s sub comm ok cut raise eff keep) ma


instance MonadState s (Blah ext err s m) where
  state f = Blah $ \s sub _ _ _ _ _ _ ->
    let (a, s') = f s
     in sub s' a $ \ext ->
          Blah $ \s' _ _ ok' _ _ _ _ -> ok' s' ext


instance Functor (Blah ext err s m) where
  fmap f (Blah fa) = Blah $ \s sub comm ok cut raise eff keep ->
    fa
      s
      (\s' a k -> sub s' (f a) $ fmap (fmap f) k)
      (\s' c1 c2 k -> comm s' c1 c2 $ fmap (fmap f) k)
      ok cut raise eff keep

instance Applicative (Blah ext err s m) where
  pure a = Blah $ \s sub _ _ _ _ _ _ ->
    sub s a $ \ext ->
      Blah $ \s' _ _ ok' _ _ _ _ -> ok' s' ext
  Blah f <*> blah@(Blah a) = Blah $ \s sub comm ok cut raise eff keep ->
    f s
      (\s' ab k ->
        a
          s'
          (\s'' a k' -> sub s'' (ab a) $ liftA2 (<*>) k k')
          (\s'' c1 c2 k' -> comm s'' c1 c2 $ \x -> fmap ab $ k' x)
          ok cut raise eff keep)
      (\s' c1 c2 k -> comm s' c1 c2 $ \x -> k x <*> blah)
      ok cut raise eff keep

instance Monad (Blah ext err s m) where
  return = pure
  Blah ma >>= f = Blah $ \s sub comm ok cut raise eff keep ->
    ma s
      (\s' a k ->
        unBlah (f a)
          s' sub
          comm
          (\s' ext ->
            unBlah (k ext >>= f)
              s' sub comm ok cut raise eff keep)
          cut raise eff keep)
      (\s' c1 c2 k -> comm s' c1 c2 $ k >=> f)
      ok cut raise eff keep


sequenceImmediateEffects
    :: Monad m
    => s
    -> ProofState ext err s m a
    -> m (ProofState ext err s m a)
sequenceImmediateEffects s =
  kill
    s
    (\s' a k' -> pure $ put s' >> Subgoal a k')
    (\s ext -> pure $ put s >> Axiom ext)
    (pure Empty)
    (\s' err -> pure $ put s' >> Throw err)
    (pure . Effect . join)
    (liftA2 (<|>))


kill
    :: Monad m
    => s
    -> (s -> a -> (ext -> ProofState ext err s m a) -> m r)
    -> (s -> ext -> m r)
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

kill s sub ok cut raise eff keep (Commit (t1 :: ProofState ext err s m x) t2 k) = do
  (x1 :: ProofState ext err s m x) <- sequenceImmediateEffects s t1
  let run_t2 sub' ok' cut' raise eff' keep' = do
        (x2 :: ProofState ext err s m x) <- sequenceImmediateEffects s t2
        kill s sub' ok' cut' raise eff' keep' $ k =<< x2

      sub' = (\s' x k' -> kill s' sub ok cut raise eff keep $ Subgoal x k' >>= k)

  kill s sub' ok
                (run_t2 sub ok cut             raise                                              eff keep)
    (\s1 err1 -> run_t2 sub ok (raise s1 err1) (\s2 err2 -> keep (raise s1 err1) (raise s2 err2)) eff keep)
    eff keep x1

kill _ _ _ cut _ _ _ Empty = cut

kill s sub ok cut raise eff keep (Handle t h k)
  = let sub' = \s' x k' -> kill s' sub ok cut raise eff keep $ Subgoal x k' >>= k
     in kill s sub' ok cut
          (\s' err -> kill s' sub' ok cut raise eff keep $ h err) eff keep t

kill s _ _ _ raise _ _ (Throw err) = raise s err

kill s _ ok _ _ _ _ (Axiom ext) = ok s ext


subgoals
    :: Monad m
    => [jdg -> ProofState ext err s m jdg]
    -> ProofState ext err s m jdg
    -> ProofState ext err s m jdg
subgoals [] p = p
subgoals (t:ts) p = do
  s <- get
  Effect $
    kill
      s
      (\s' a k' -> pure $ put s' >> applyCont (subgoals ts . k') (t a))
      (\s' ext -> pure $ put s' >> Axiom ext)
      (pure Empty)
      (\s' err -> pure $ put s' >> Throw err)
      (pure . Effect . join)
      (liftA2 (<|>))
      p

-- gather
--     :: Monad m
--     => TacticT jdg ext err s m a
--     -> ([(a, jdg)] -> TacticT jdg ext err s m a)
--     -> TacticT jdg ext err s m a
-- gather (TacticT t) f = TacticT $ StateT $ \jdg -> do
--   let p = runStateT t jdg
--   s <- get
--   Effect $
--     kill
--       s
--       (\s' (a, jdg) k' -> pure $ put s' >> applyCont k' $ f (a, jdg))
--       (\s' ext -> pure $ put s' >> Axiom ext)
--       (pure Empty)
--       (\s' err -> pure $ put s' >> Throw err)
--       (pure . Effect . join)
--       (liftA2 (<|>))
--       p

(<@>)
    :: Monad m
    => TacticT jdg ext err s m a
    -> [TacticT jdg ext err s m a]
    -> TacticT jdg ext err s m a
TacticT t <@> ts =
  TacticT $ StateT $ \jdg ->
    subgoals (fmap (\(TacticT t') (_, jdg') -> runStateT t' jdg') ts) $ runStateT t jdg


data Result s jdg err ext
  = ErrorResult err
  | Extract s ext [jdg]
  | NoResult
  deriving stock (Show, Generic, Eq)


-- (<@>) :: Functor m => TacticT jdg ext err s m a -> [TacticT jdg ext err s m a] -> TacticT jdg ext err s m a
-- (<@>) t [] = t
-- (<@>) t (s : ss) = kill _ _ _ _ _ _ _ t


proof
    :: MonadExtract ext m
    => s
    -> ProofState ext err s m jdg
    -> m [Result s jdg err ext]
proof s =
  kill s
    (\s' _ x -> proof s' $ x =<< lift hole)
    (\s ext -> pure . pure $ Extract s ext [])
    (pure [])
    (const $ pure . pure . ErrorResult)
    join
    (liftA2 (<>))

class MonadSlip m where
  slip :: m (r -> x) -> r -> m x


proofgoals
    :: MonadExtract ext m
    => ([jdg] -> Maybe err)
    -> s
    -> ProofState ext err s m jdg
    -> m ([jdg] -> ProofState ext err s m jdg)
proofgoals f s =
  kill s
    (\s' jdg k -> do
      r <- proofgoals f s' $ k =<< lift hole
      pure $ \goals -> r $ jdg : goals
      )
    (\s' ext -> pure $ \goals -> put s' >>
      case f goals of
        Just err -> Throw err
        Nothing -> Axiom ext
    )
    (pure $ const empty)
    (\s' err -> pure $ const $ put s' >> Throw err)
    (\mma -> pure $ \goals -> Effect $ fmap ($ goals) $ join mma)
    (liftA2 $ liftA2 (<|>))


pruning
    :: MonadExtract ext m
    => TacticT jdg ext err s m ()
    -> ([jdg] -> Maybe err)
    -> TacticT jdg ext err s m ()
pruning (TacticT t) f = do
  s <- get
  TacticT $ StateT $ \jdg -> do
    let t' = execStateT t jdg
    go <- lift $ proofgoals f s t'
    fmap ((), ) $ go []


runTactic
    :: MonadExtract ext m
    => s
    -> jdg
    -> TacticT jdg ext err s m a -> m [Result s jdg err ext]
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

newtype Tactic2 jdg ext err s m a = Tactic2
  { unTactic2 :: StateT jdg (Blah ext err s m) a
  } deriving newtype (Functor, Applicative, Monad, Alternative, MonadPlus)


commit2 :: Tactic2 jdg ext err s m a -> Tactic2 jdg ext err s m a -> Tactic2 jdg ext err s m a
commit2 (Tactic2 t1) (Tactic2 t2) = tactic2 $ \jdg ->
  Blah $ \s _ comm _ _ _ _ _ ->
    comm s (runStateT t1 jdg) (runStateT t2 jdg) pure


catch2
    :: Tactic2 jdg ext err s m a
    -> (err -> Tactic2 jdg ext err s m a)
    -> Tactic2 jdg ext err s m a
catch2 (Tactic2 t) h = tactic2 $ \jdg ->
  Blah $ \s sub comm ok cut raise eff keep ->
    unBlah (runStateT t jdg)
      s sub comm ok cut
      (\s' err -> unBlah (tacticToBlah jdg $ h err) s' sub comm ok cut raise eff keep)
      eff keep

tacticToBlah :: jdg -> Tactic2 jdg ext err s m a -> Blah ext err s m (a, jdg)
tacticToBlah jdg (Tactic2 t) = runStateT t jdg

tactic2 :: (jdg -> Blah ext err s m (a, jdg)) -> Tactic2 jdg ext err s m a
tactic2 f = Tactic2 $ StateT $ f

goal2 :: Tactic2 jdg ext err s m jdg
goal2 = Tactic2 get

throw2 :: err -> Tactic2 jdg ext err s m a
throw2 err = Tactic2 $ lift $ Blah $ \s _ _ _ _ raise _ _ -> raise s err


sequenceImmediateEffects2 :: Monad m => s -> Blah ext err s m a -> m (Blah ext err s m a)
sequenceImmediateEffects2 s (Blah m) =
  m s
    (\s' a k -> pure $ do
      put s'
      Blah $ \s'' sub _ _ _ _ _ _ -> sub s'' a k
      )
    (\s' c1 c2 k -> pure $ do
      put s'
      Blah $ \s'' _ comm _ _ _ _ _ -> comm s'' c1 c2 k)
    (\s' ext -> pure $ do
      put s'
      Blah $ \s'' _ _ ok _ _ _ _ -> ok s'' ext
    )
    (pure empty)
    (\s' err -> pure $ do
      put s'
      Blah $ \s'' _ _ _ _ raise _ _ -> raise s'' err
    )
    join
    (liftA2 (<|>))


kill2
  :: forall s m a ext err r
   . Monad m
  => s
  -> (s -> a -> (ext -> Blah ext err s m a) -> m r)
  -> (s -> ext -> m r)
  -> m r
  -> (s -> err -> m r)
  -> (m (m r) -> m r)
  -> (m r -> m r -> m r)
  -> Blah ext err s m a
  -> m r
kill2 s sub ok cut raise eff keep (Blah m) =
  m
    s sub
    (\s' c1 c2 k -> do
      let run_c2
            :: m r
            -> (s -> err -> m r)
            -> m r
          run_c2 cut' raise' = do
            x2 <- sequenceImmediateEffects2 s' c2
            kill2 s' sub ok cut' raise' eff keep
              $ k =<< x2

      x1 <- sequenceImmediateEffects2 s' c1
      kill2
        s' sub ok
        (run_c2 cut raise)
        (\s1 err1 ->
          run_c2
            (raise s1 err1)
            (\s2 err2 -> keep (raise s1 err1) (raise s2 err2)))
        eff keep
          $ k =<< x1
    )
    ok cut raise eff keep


proof2 :: MonadExtract ext m => s -> Blah ext err s m a -> m [Result s jdg err ext]
proof2 s =
  kill2
    s
    (\s' _ x -> proof2 s' . x =<< hole)
    (\s' ext -> pure $ pure $ Extract s' ext [])
    (pure $ pure $ NoResult)
    (\_ err -> pure $ pure $ ErrorResult err)
    join
    (liftA2 (<>))

ignore :: Functor m => TacticT jdg ext err s m ()
ignore = pure ()

