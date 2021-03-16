module Wingman.KnownStrategies where

import Control.Monad.Error.Class
import OccName (mkVarOcc)
import Refinery.Tactic
import Wingman.Context (getCurrentDefinitions)
import Wingman.KnownStrategies.QuickCheck (deriveArbitrary)
import Wingman.Machinery (tracing)
import Wingman.Tactics
import Wingman.Types


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
  apps <- applicable_applies
  recs <- can_recurse

  let apps' = apps ++ recs
  choice
    [ choice $ fmap applyApply apps'
    , assumption
    ]

