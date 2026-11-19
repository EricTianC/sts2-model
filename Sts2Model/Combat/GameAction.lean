/-
  Multiplayer-deterministic GameAction queue and ActionExecutor modeling.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.GameActions/GameAction.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.GameActions/ActionExecutor.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.GameActions/PlayCardAction.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.GameActions/EndPlayerTurnAction.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.GameActions/UndoEndPlayerTurnAction.cs`
-/
import Sts2Model.Core.Ids
import Sts2Model.Model.State

namespace Sts2Model.Combat

open Sts2Model.Core
open Sts2Model.Model

/-- Deterministic player-driven combat actions replicated across multiplayer peers.
    Ref: `Core.GameActions/*.cs`. -/
inductive GameAction where
  | playCard (playerId : PlayerId) (cardId : CardInstanceId) (targetId : Option CreatureId)
  | usePotion (playerId : PlayerId) (slotIdx : Nat) (targetId : Option CreatureId)
  | discardPotion (playerId : PlayerId) (slotIdx : Nat)
  | endPlayerTurn (playerId : PlayerId) (canBackOut : Bool := true)
  | undoEndPlayerTurn (playerId : PlayerId)
  | readyToBeginEnemyTurn (playerId : PlayerId)
  deriving Repr, DecidableEq

/-- Ordered queue of synchronized game actions. -/
abbrev ActionQueue := List GameAction

/-- Execution status of `ActionExecutor`. Ref: `Core.GameActions/ActionExecutor.cs`. -/
structure ActionExecutorState where
  isPaused   : Bool := false
  isCanceled : Bool := false
  executedCount : Nat := 0
  deriving Repr, DecidableEq, Inhabited

end Sts2Model.Combat
