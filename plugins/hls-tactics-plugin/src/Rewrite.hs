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
      -> (s -> ext -> r)
      -> r
      -> (s -> err -> r)
      -> (m r -> r)
      -> (r -> r -> r)
      -> r
  }

instance Alternative (ProofState ext err s m) where
  ProofState m1 <|> ProofState m2 = ProofState $ \s sub ok cut raise eff alt ->
    alt (m1 s sub ok cut raise eff alt) (m2 s sub ok cut raise eff alt)
  empty = ProofState $ \_ _ _ cut _ _ _ -> cut

instance MonadPlus (ProofState ext err s m) where

instance MonadTrans (ProofState ext err s) where
  lift ma = ProofState $ \s sub ok cut raise eff alt -> eff $
    fmap (\a -> runProofState (pure a) s sub ok cut raise eff alt) ma


instance MonadState s (ProofState ext err s m) where
  state f = ProofState $ \s sub _ _ _ _ _ ->
    let (a, s') = f s
     in sub s' a $ \ext ->
          ProofState $ \s' _ ok' _ _ _ _ -> ok' s' ext


instance Functor (ProofState ext err s m) where
  fmap f (ProofState fa) = ProofState $ \s sub ok cut raise eff alt ->
    fa
      s
      (\s' a k -> sub s' (f a) $ fmap (fmap f) k)
      ok cut raise eff alt

instance Applicative (ProofState ext err s m) where
  pure a = ProofState $ \s sub _ _ _ _ _ ->
    sub s a $ \ext ->
      ProofState $ \s' _ ok' _ _ _ _ -> ok' s' ext
  ProofState f <*> ProofState a = ProofState $ \s sub ok cut raise eff alt ->
    f s
      (\s' ab k ->
        a
          s'
          (\s'' a k' -> sub s'' (ab a) $ liftA2 (<*>) k k')
          ok cut raise eff alt)
      ok cut raise eff alt

instance Monad (ProofState ext err s m) where
  return = pure
  ProofState ma >>= f = ProofState $ \s sub ok cut raise eff alt ->
    ma s
      (\s' a k ->
        runProofState (applyCont (f <=< k) $ f a)
          s'
          sub
          ok
          cut raise eff alt)
      ok cut raise eff alt

applyCont :: (ext -> ProofState ext err s m a) -> ProofState ext err s m a -> ProofState ext err s m a
applyCont k (ProofState m) = ProofState $ \s sub ok cut raise eff alt ->
  m
    s
    (\s' a k' -> sub s' a $ applyCont k . k')
    (\s' ext -> runProofState (k ext) s' sub ok cut raise eff alt)
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
      (\s a _ ->
        mconcat
          [ "(put "
          , showsPrec 10 s ""
          , " >> sg "
          , showsPrec 10 a ""
          , " <k>"
          , ")"
          ])
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
    ProofState $ \s sub _ _ _ _ _ ->
      let (a, s') = f s
       in sub s' (a, jdg) $ \ext ->
          ProofState $ \s'' _ ok' _ _ _ _ -> ok' s'' ext


commit
    :: forall s jdg ext err m a
     . TacticT jdg ext err s m a
    -> TacticT jdg ext err s m a
    -> TacticT jdg ext err s m a
commit (TacticT t1) (TacticT t2) = tactic2 $ \jdg -> do
  ProofState $ \s sub ok cut raise eff (alt :: r -> r -> r) -> do
    let run_c2
          :: r
          -> (s -> err -> r)
          -> r
        run_c2 cut' raise' = do
          runProofState (runStateT t2 jdg) s sub ok cut' raise' eff alt

    runProofState (runStateT t1 jdg)
      s
      sub
      ok
      (run_c2 cut raise)
      (\s1 err1 ->
        run_c2
          (raise s1 err1)
          (\s2 err2 -> alt (raise s1 err1) (raise s2 err2)))
      eff alt


catch
    :: TacticT jdg ext err s m a
    -> (err -> TacticT jdg ext err s m a)
    -> TacticT jdg ext err s m a
catch (TacticT t) h = tactic2 $ \jdg ->
  ProofState $ \s sub ok cut raise eff alt ->
    runProofState (runStateT t jdg)
      s sub ok cut
      (\s' err -> runProofState (tacticToBlah jdg $ h err) s' sub ok cut raise eff alt)
      eff alt


tacticToBlah :: jdg -> TacticT jdg ext err s m a -> ProofState ext err s m (a, jdg)
tacticToBlah jdg (TacticT t) = runStateT t jdg


tactic2 :: (jdg -> ProofState ext err s m (a, jdg)) -> TacticT jdg ext err s m a
tactic2 f = TacticT $ StateT $ f


goal :: TacticT jdg ext err s m jdg
goal = TacticT get


throw :: err -> TacticT jdg ext err s m a
throw err = TacticT $ lift $ ProofState $ \s _ _ _ raise _ _ -> raise s err


subgoals
    :: Monad m
    => [jdg -> ProofState ext err s m jdg]
    -> ProofState ext err s m jdg
    -> ProofState ext err s m jdg
subgoals [] p = p
subgoals (t:ts) (ProofState p) =
  ProofState $ \s sub ok cut raise eff alt ->
    p
      s
      (\s' jdg k ->
        runProofState (applyCont (subgoals ts . k) $ t jdg)
          s' sub ok cut raise eff alt
      )
      ok cut raise eff alt


(<@>)
    :: Monad m
    => TacticT jdg ext err s m a
    -> [TacticT jdg ext err s m a]
    -> TacticT jdg ext err s m a
TacticT t <@> ts =
  TacticT $ StateT $ \jdg ->
    subgoals (fmap (\(TacticT t') (_, jdg') -> runStateT t' jdg') ts) $
      runStateT t jdg


proof :: MonadExtract ext m => s -> ProofState ext err s m a -> m [Result s err ext]
proof s p =
  runProofState p
    s
    (\s' _ x -> proof s' . x =<< hole)
    (\s' ext -> pure $ pure $ Extract s' ext)
    (pure $ pure $ NoResult)
    (\_ err -> pure $ pure $ ErrorResult err)
    (\ma -> do
      r <- join ma
      pure r
    )
    (liftA2 (<>))


rule :: Functor m => Rule jdg ext err s m ext -> TacticT jdg ext err s m ()
rule r = TacticT $ StateT $ const $ fmap ((),) $ ruleToProofState r


ruleToProofState
    :: Functor m
    => Rule jdg ext err s m ext
    -> ProofState ext err s m jdg
ruleToProofState r = ProofState $ \s sub ok cut raise eff alt ->
  case r of
    Pure ext ->
      ok s ext
    SubgoalR jdg k ->
      sub s jdg $ \ext -> ruleToProofState (k ext)
    EffectR m ->
      eff $ fmap (\r' -> runProofState (ruleToProofState r') s sub ok cut raise eff alt) m
    StatefulR f ->
      let (s', r') = f s
       in runProofState (ruleToProofState r') s' sub ok cut raise eff alt


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
  TacticT $ lift $ ProofState $ \s sub _ _ _ _ _ ->
    sub s a $ fmap fst . tacticToBlah jdg . k


axiom :: ext -> TacticT jdg ext err s m a
axiom ext = TacticT $ lift $ ProofState $ \s _ ok _ _ _ _ ->
  ok s ext

debug :: String -> ProofState ext err s m a -> ProofState ext err s m a
debug = debug' anythingToString anythingToString anythingToString


debug' :: (ext -> String) -> (err -> String) -> (s -> String) -> String -> ProofState ext err s m a -> ProofState ext err s m a
debug' showExt showErr showS lbl (ProofState p) = do
  let l = debugLog showExt showErr showS lbl
  ProofState $ \s sub ok cut raise eff alt ->
    p s
      (\s' a k     -> flip trace (sub s' a k)      $ l $ DbgSub s' $ anythingToString a)
      (\s' ext     -> flip trace (ok s' ext)       $ l $ DbgOk s' ext)
      (               flip trace cut               $ l $ DbgCut)
      (\s' err     -> flip trace (raise s' err)    $ l $ DbgRaise s' err)
      (\mma        -> flip trace (eff mma)         $ l $ DbgEff)
      (\r1 r2      -> flip trace (alt r1 r2)       $ l $ DbgAlt)


debugLog :: (ext -> String) -> (err -> String) -> (s -> String) -> String -> DbgItem ext err s -> String
debugLog showExt showErr showS lbl item =
  mconcat
    [ "> "
    , lbl
    , ": "
    , case item of
       (DbgSub s x)     -> "sub\n  - State " <> showS s <> "\n  - Value " <> x
       (DbgOk s ext)    -> "ok\n  - State " <> showS s <> "\n  - Extract " <> showExt ext
       DbgCut           -> "cut"
       (DbgRaise s err) -> "raise\n  - State " <> showS s <> "\n  - Error " <> showErr err
       DbgEff           -> "eff"
       DbgAlt           -> "alt"
    ]

data DbgItem ext err s
  = DbgSub s String
  | DbgOk s ext
  | DbgCut
  | DbgRaise s err
  | DbgEff
  | DbgAlt

