{-# OPTIONS_GHC -Wno-deprecations #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Rewrite.Test.SanityCheck where


import Rewrite.Test.Spec (testJdg2)
import Control.Applicative
import Rewrite.Test.STLC (Term (..), Judgement (..), Type (..))
import Data.Functor.Identity
import Refinery.Tactic
import Refinery.Tactic.Internal
import Refinery.ProofState
import Control.Monad.Error

peek :: (ext -> TacticT jdg ext err s m ()) -> TacticT jdg ext err s m ()
peek k = tactic $ \j -> Subgoal ((), j) $ \e -> proofState (k e) j

type NoEffects = TacticT Judgement Term String Int Identity

instance MonadExtract Term Identity where
  hole = pure Hole

lam :: Monad m => TacticT Judgement Term String s m ()
lam = rule $ \jdg ->
  case jdg of
    hy :- (t :-> a) -> do
      let name = "x"
      ext <- subgoal $ (("x", t) : hy) :- a
      pure $ Lam name ext
    _ -> throwError "not a lambda"

test :: IO ()
test = do
  let (x :: NoEffects ()) = do
        peek $ \case
          Lam _ Hole -> throwError "incomplete"
          _ -> pure ()
        lam <|> pure ()

  print $ fmap (fmap (\(t, _, _) -> t)) $ runIdentity $ runTacticT x testJdg2 2

