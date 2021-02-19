module Copilot.Auto where

import Control.Monad.State (gets)
import Copilot.Context
import Copilot.Judgements
import Copilot.KnownStrategies
import Copilot.Machinery (tracing)
import Copilot.Tactics
import Copilot.Types
import Refinery.Tactic


------------------------------------------------------------------------------
-- | Automatically solve a goal.
auto :: TacticsM ()
auto = do
  jdg <- goal
  skolems <- gets ts_skolems
  current <- getCurrentDefinitions
  traceMX "goal" jdg
  traceMX "ctx" current
  traceMX "skolems" skolems
  commit knownStrategies
    . tracing "auto"
    . localTactic (auto' 4)
    . disallowing RecursiveCall
    $ fmap fst current

