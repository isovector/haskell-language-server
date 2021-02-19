{-# LANGUAGE LambdaCase #-}

module Copilot.KnownStrategies where

import Control.Monad.Error.Class
import Copilot.Context (getCurrentDefinitions)
import Copilot.Tactics
import Copilot.Types
import OccName (mkVarOcc)
import Refinery.Tactic
import Copilot.Machinery (tracing)
import Copilot.KnownStrategies.QuickCheck (deriveArbitrary)


knownStrategies :: TacticsM ()
knownStrategies = choice
  [ known "fmap" deriveFmap
  , known "arbitrary" deriveArbitrary
  ]


known :: String -> TacticsM () -> TacticsM ()
known name t = do
  getCurrentDefinitions >>= \case
    [(def, _)] | def == mkVarOcc name ->
      tracing ("known " <> name) t
    _ -> throwError NoApplicableTactic


deriveFmap :: TacticsM ()
deriveFmap = do
  try intros
  overAlgebraicTerms homo
  choice
    [ overFunctions apply >> auto' 2
    , assumption
    , recursion
    ]

