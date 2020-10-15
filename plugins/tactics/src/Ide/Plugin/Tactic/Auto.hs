module Ide.Plugin.Tactic.Auto where

import Ide.Plugin.Tactic.Context
import Ide.Plugin.Tactic.Judgements
import Ide.Plugin.Tactic.KnownStrategies
import Ide.Plugin.Tactic.Tactics
import Ide.Plugin.Tactic.Types
import Refinery.Tactic
import Ide.Plugin.Tactic.Machinery (tracing)
import Control.Monad.State.Class (gets)


------------------------------------------------------------------------------
-- | Automatically solve a goal.
auto :: TacticsM ()
auto = do
  jdg <- goal
  current <- getCurrentDefinitions
  skolems <- gets ts_skolems
  traceMX "goal" jdg
  traceMX "ctx" current
  traceMX "skolems" skolems
  commit knownStrategies
    . tracing "auto"
    . localTactic (auto' 4)
    . disallowing
    $ fmap fst current

