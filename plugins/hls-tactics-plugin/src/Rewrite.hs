{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE RankNTypes #-}

module Rewrite where

import GHC.Generics
import Control.Monad.State.Strict
import Control.Applicative
import Test.QuickCheck.Classes ()
import GHC.Generics (Generic)
import Data.Tuple (swap)
import Debug.RecoverRTTI
import Debug.Trace (trace)
import Debug.Trace (traceM)

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


deriving instance (Show a, Show jdg, Show (m (Rule jdg ext err s m a))) =>
  Show (Rule jdg ext err s m a)

instance Functor m => MonadState s (Rule jdg ext err s m) where
  state s =  StatefulR $ fmap (fmap pure . swap) s

instance MonadTrans (Rule jdg ext err s) where
  lift = EffectR . fmap pure


instance Functor m => Applicative (Rule jdg ext err s m) where
  pure a = Pure a
  (<*>) = ap


instance Functor m => Monad (Rule jdg ext err s m) where
  return = pure
  (>>=) (Pure a) f = f a
  (>>=) (SubgoalR jdg k) f = SubgoalR jdg $ f <=< k
  (>>=) (EffectR m) f = EffectR $ fmap (f =<<) m
  (>>=) (StatefulR m) f = StatefulR $ fmap (fmap (f =<<)) m


subgoal :: Functor m => jdg -> Rule jdg ext err s m ext
subgoal jdg = SubgoalR jdg pure



class Monad m => MonadExtract ext m | m -> ext where
  hole :: m ext


data ProofState ext err s m a = ProofState
  { runProofState
      :: forall r
       . s
      -> (s -> a -> (ext -> ProofState ext err s m a) -> r)
      -> (forall x
            . s
           -> ProofState ext err s m x
           -> ProofState ext err s m x
           -> (x -> ProofState ext err s m a)
           -> r
         )
      -> (s -> ext -> r)
      -> r
      -> (s -> err -> r)
      -> (m r -> r)
      -> (r -> r -> r)
      -> r
  }

instance Alternative (ProofState ext err s m) where
  ProofState m1 <|> ProofState m2 = ProofState $ \s sub comm ok cut raise eff alt ->
    alt (m1 s sub comm ok cut raise eff alt) (m2 s sub comm ok cut raise eff alt)
  empty = ProofState $ \_ _ _ _ cut _ _ _ -> cut

instance MonadPlus (ProofState ext err s m) where

instance MonadTrans (ProofState ext err s) where
  lift ma = ProofState $ \s sub comm ok cut raise eff alt -> eff $
    fmap (\a -> runProofState (pure a) s sub comm ok cut raise eff alt) ma


instance MonadState s (ProofState ext err s m) where
  state f = ProofState $ \s sub _ _ _ _ _ _ ->
    let (a, s') = f s
     in sub s' a $ \ext ->
          ProofState $ \s' _ _ ok' _ _ _ _ -> ok' s' ext


instance Functor (ProofState ext err s m) where
  fmap f (ProofState fa) = ProofState $ \s sub comm ok cut raise eff alt ->
    fa
      s
      (\s' a k -> sub s' (f a) $ fmap (fmap f) k)
      (\s' c1 c2 k -> comm s' c1 c2 $ fmap (fmap f) k)
      ok cut raise eff alt

instance Applicative (ProofState ext err s m) where
  pure a = ProofState $ \s sub _ _ _ _ _ _ ->
    sub s a $ \ext ->
      ProofState $ \s' _ _ ok' _ _ _ _ -> ok' s' ext
  (<*>) = ap
  -- ProofState f <*> blah@(ProofState a) = ProofState $ \s sub comm ok cut raise eff alt ->
  --   f s
  --     (\s' ab k ->
  --       a
  --         s'
  --         (\s'' a k' -> sub s'' (ab a) $ liftA2 (<*>) k k')
  --         (\s'' c1 c2 k' -> comm s'' c1 c2 $ \x -> fmap ab $ k' x)
  --         ok cut raise eff alt)
  --     (\s' c1 c2 k -> comm s' c1 c2 $ \x -> k x <*> blah)
  --     ok cut raise eff alt

instance Monad (ProofState ext err s m) where
  return = pure
  ProofState ma >>= f = ProofState $ \s sub comm ok cut raise eff alt ->
    ma s
      (\s' a k ->
        runProofState (applyCont (f <=< k) $ f a)
          s'
          sub
          comm
          ok
          cut raise eff alt)
      (\s' c1 c2 k -> comm s' c1 c2 $ k >=> f)
      ok cut raise eff alt

applyCont :: (ext -> ProofState ext err s m a) -> ProofState ext err s m a -> ProofState ext err s m a
applyCont k (ProofState m) = ProofState $ \s sub comm ok cut raise eff alt ->
  m
    s
    (\s' a k' -> sub s' a $ applyCont k . k')
    (\s' c1 c2 k' -> comm s' c1 c2 $ applyCont k . k')
    (\s' ext -> runProofState (k ext) s' sub comm ok cut raise eff alt)
    cut
    raise
    eff
    alt



data Result s err ext
  = ErrorResult err
  | Extract s ext
  | NoResult
  deriving stock (Show, Generic, Eq)


newtype TacticT jdg ext err s m a = TacticT
  { unTactic2 :: StateT jdg (ProofState ext err s m) a
  } deriving newtype (Functor, Applicative, Monad, Alternative, MonadPlus)

instance MonadTrans (TacticT jdg ext err s) where
  lift = TacticT . lift . lift

instance (Show s, Monoid ext, Show a, Show ext, Show err, Monoid s, Monoid jdg, Show (m String)) => Show (TacticT jdg ext err s m a) where
  show (TacticT t) =
    show $ evalStateT t mempty

instance (Show s, Monoid ext, Show a, Show ext, Show err, Monoid s, Show (m String)) => Show (ProofState ext err s m a) where
  show t =
    runProofState t
      mempty
      (\s a k ->
        mconcat
          [ "(put "
          , showsPrec 10 s ""
          , " >> sg "
          , showsPrec 10 a ""
          , " <k>"
          , ")"
          ])
      (\_ _c1 _c2 _k -> "(commit <c1> <c2>)")
        -- mconcat
        --   [ show $ tactic2 $ \jdg -> fmap (, jdg) c2
        --   ])
      (\s ext ->
        mconcat
          [ "(put "
          , showsPrec 10 s ""
          , " >> axiom ("
          , show ext
          , "))"
          ])
      "empty"
      (\s err ->
        mconcat
          [ "(put "
          , showsPrec 10 s ""
          , " >> throw "
          , show err
          , ")"
          ])
      show
      (\s1 s2 ->
        mconcat
          [ "("
          , s1
          , " <|> "
          , s2
          , ")"
          ])


instance MonadState s (TacticT jdg ext err s m) where
  state f = TacticT $ StateT $ \jdg ->
    ProofState $ \s sub _ _ _ _ _ _ ->
      let (a, s') = f s
       in sub s' (a, jdg) $ \ext ->
          ProofState $ \s'' _ _ ok' _ _ _ _ -> ok' s'' ext


commit :: TacticT jdg ext err s m a -> TacticT jdg ext err s m a -> TacticT jdg ext err s m a
commit (TacticT t1) (TacticT t2) = tactic2 $ \jdg ->
  ProofState $ \s _ comm _ _ _ _ _ ->
    comm s (runStateT t1 jdg) (runStateT t2 jdg) pure


catch
    :: TacticT jdg ext err s m a
    -> (err -> TacticT jdg ext err s m a)
    -> TacticT jdg ext err s m a
catch (TacticT t) h = tactic2 $ \jdg ->
  ProofState $ \s sub comm ok cut raise eff alt ->
    runProofState (runStateT t jdg)
      s sub comm ok cut
      (\s' err -> runProofState (tacticToBlah jdg $ h err) s' sub comm ok cut raise eff alt)
      eff alt

tacticToBlah :: jdg -> TacticT jdg ext err s m a -> ProofState ext err s m (a, jdg)
tacticToBlah jdg (TacticT t) = runStateT t jdg

tactic2 :: (jdg -> ProofState ext err s m (a, jdg)) -> TacticT jdg ext err s m a
tactic2 f = TacticT $ StateT $ f

goal :: TacticT jdg ext err s m jdg
goal = TacticT get

throw :: err -> TacticT jdg ext err s m a
throw err = TacticT $ lift $ ProofState $ \s _ _ _ _ raise _ _ -> raise s err


sequenceImmediateEffects :: forall m s ext err a. Monad m => s -> ProofState ext err s m a -> m (ProofState ext err s m a)
sequenceImmediateEffects s (ProofState m) =
  m s
    (\s' a k -> pure $ do
      put s'
      ProofState $ \s'' sub _ _ _ _ _ _ -> sub s'' a k
      )
    (\s' c1 c2 k -> pure $ do
      put s'
      ProofState $ \s'' _ comm _ _ _ _ _ -> comm s'' c1 c2 k)
    (\s' ext -> pure $ do
      put s'
      ProofState $ \s'' _ _ ok _ _ _ _ -> ok s'' ext
    )
    (pure empty)
    (\s' err -> pure $ do
      put s'
      ProofState $ \s'' _ _ _ _ raise _ _ -> raise s'' err
    )
    (\mma -> pure $
      ProofState $ \s' sub comm ok cut raise eff alt ->
        eff $ do
          ma <- mma
          a <- ma
          kill
            s'
            (\s'' a k -> pure $ sub s'' a k)
            (\s'' ext -> pure $ ok s'' ext)
            (pure cut)
            (\s'' err -> pure $ raise s'' err)
            join
            (liftA2 alt)
            a
    )
    (liftA2 (<|>))


kill
  :: forall s m a ext err r
   . Monad m
  => s
  -> (s -> a -> (ext -> ProofState ext err s m a) -> m r)
  -> (s -> ext -> m r)
  -> m r
  -> (s -> err -> m r)
  -> (m (m r) -> m r)
  -> (m r -> m r -> m r)
  -> ProofState ext err s m a
  -> m r
kill s sub ok cut raise eff alt (ProofState m) = do
  m
    s sub
    (\s' c1 c2 k -> do
      let run_c2
            :: m r
            -> (s -> err -> m r)
            -> m r
          run_c2 cut' raise' = do
            x2 <- sequenceImmediateEffects s' c2
            kill s' sub ok cut' raise' eff alt
              $ k =<< x2

      x1 <- sequenceImmediateEffects s' c1
      kill
        s'
        (\s'' x k' -> kill s'' sub ok cut raise eff alt $ applyCont k' (pure x) >>= k)
        ok
        (run_c2 cut raise)
        (\s1 err1 ->
          run_c2
            (raise s1 err1)
            (\s2 err2 -> alt (raise s1 err1) (raise s2 err2)))
        eff alt x1
    )
    ok cut raise
    eff
    alt


proof :: MonadExtract ext m => s -> ProofState ext err s m a -> m [Result s err ext]
proof s =
  kill
    s
    (\s' _ x -> proof s' . x =<< hole)
    (\s' ext -> pure $ pure $ Extract s' ext)
    (pure $ pure $ NoResult)
    (\_ err -> pure $ pure $ ErrorResult err)
    join
    (liftA2 (<>))


rule :: Functor m => Rule jdg ext err s m ext -> TacticT jdg ext err s m ()
rule r = TacticT $ StateT $ const $ fmap ((),) $ ruleToProofState r


ruleToProofState
    :: Functor m
    => Rule jdg ext err s m ext
    -> ProofState ext err s m jdg
ruleToProofState r = ProofState $ \s sub comm ok cut raise eff alt ->
  case r of
    Pure ext ->
      ok s ext
    SubgoalR jdg k ->
      sub s jdg $ \ext -> ruleToProofState (k ext)
    EffectR m ->
      eff $ fmap (\r' -> runProofState (ruleToProofState r') s sub comm ok cut raise eff alt) m
    StatefulR f ->
      let (s', r') = f s
       in runProofState (ruleToProofState r') s' sub comm ok cut raise eff alt


runTactic
    :: MonadExtract ext m
    => s
    -> jdg
    -> TacticT jdg ext err s m a
    -> m [Result s err ext]
runTactic s jdg (TacticT t) =
  proof s (flip evalStateT jdg $ t)


sg
    :: a
    -> (ext -> TacticT jdg ext err s m a)
    -> TacticT jdg ext err s m a
sg a k = do
  jdg <- goal
  TacticT $ lift $ ProofState $ \s sub _ _ _ _ _ _ ->
    sub s a $ fmap fst . tacticToBlah jdg . k


axiom :: ext -> TacticT jdg ext err s m a
axiom ext = TacticT $ lift $ ProofState $ \s _ _ ok _ _ _ _ ->
  ok s ext

