/-
  CombatState, PendingLossState, CombatHistoryEntry, and RunState models.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Combat/CombatState.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Combat/PendingLossState.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Runs/RunState.cs`
-/
import Sts2Model.Core.Dec
import Sts2Model.Core.Ids
import Sts2Model.Core.Enums
import Sts2Model.Core.Rng
import Sts2Model.Model.Creature
import Sts2Model.Model.Player

namespace Sts2Model.Model

open Sts2Model.Core

/-- Entries recorded in combat history (used by MelodyCmd, card counters, etc.).
    Ref: `Core.Combat.History/CombatHistory.cs` & `Entries/*.cs`. -/
inductive CombatHistoryEntry where
  | cardPlayStarted (round : Nat) (side : CombatSide) (play : CardPlay) (tags : List CardTag)
  | cardPlayFinished (round : Nat) (side : CombatSide) (play : CardPlay) (tags : List CardTag)
  | energySpent (round : Nat) (playerId : PlayerId) (amount : Nat)
  | starsModified (round : Nat) (playerId : PlayerId) (delta : Int)
  | powerReceived (round : Nat) (powerId : ModelId) (targetId : CreatureId) (amount : Int)
  | damageDealt (round : Nat) (dealerId : Option CreatureId) (result : DamageResult)
  deriving Repr, DecidableEq

/-- Pending loss waiting to be processed at the next safe point.
    Ref: `Core.Combat/PendingLossState.cs`. -/
structure PendingLossState where
  roomId : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- Readiness tracking per player for ending turn (supports multiplayer undo).
    Ref: `Core.Combat/CombatManager.cs`. -/
structure PlayerTurnReadyState where
  playerId   : PlayerId
  readyToEnd : Bool := false
  canBackOut : Bool := true
  readyForEnemyTurn : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Complete mutable combat state. Ref: `Core.Combat/CombatState.cs`. -/
structure CombatState where
  combatId         : CombatId := 1
  roundNumber      : Nat := 1
  currentSide      : CombatSide := .player
  isInProgress     : Bool := true
  isEnding         : Bool := false
  allies           : List Creature := []
  enemies          : List Creature := []
  players          : List Player := []
  modifiers        : List ModelId := []
  badges           : List ModelId := []
  runModels        : List ModelId := []
  dominion         : Option ModelId := none
  pendingLoss      : Option PendingLossState := none
  history          : List CombatHistoryEntry := []
  rng              : Rng := Rng.ofSeed 0
  nextInstanceId   : Nat := 1000
  turnReady        : List PlayerTurnReadyState := []
  ascensionLevel   : Nat := 0
  /-- Optional specialized streams for runs; v1 trace combat keeps its single legacy stream. -/
  shuffleRng        : Option Rng := none
  monsterAiRng      : Option Rng := none
  deriving Repr, DecidableEq, Inhabited

namespace CombatState

def allCreatures (cs : CombatState) : List Creature :=
  cs.allies ++ cs.enemies

def findCreature (cs : CombatState) (cid : CreatureId) : Option Creature :=
  cs.allCreatures.find? (·.id == cid)

def containsCreature (cs : CombatState) (cid : CreatureId) : Bool :=
  cs.allCreatures.any (·.id == cid)

def updateCreature (cs : CombatState) (cid : CreatureId) (f : Creature → Creature) : CombatState :=
  { cs with
    allies  := cs.allies.map fun c => if c.id == cid then f c else c
    enemies := cs.enemies.map fun c => if c.id == cid then f c else c }

def findPlayer (cs : CombatState) (pid : PlayerId) : Option Player :=
  cs.players.find? (·.playerId == pid)

def updatePlayer (cs : CombatState) (pid : PlayerId) (f : Player → Player) : CombatState :=
  { cs with players := cs.players.map fun p => if p.playerId == pid then f p else p }

def getOpponentsOf (cs : CombatState) (side : CombatSide) : List Creature :=
  match side with
  | .player => cs.enemies
  | .enemy  => cs.allies
  | .none   => []

def getTeammatesOf (cs : CombatState) (side : CombatSide) : List Creature :=
  match side with
  | .player => cs.allies
  | .enemy  => cs.enemies
  | .none   => []

def hittableEnemies (cs : CombatState) : List Creature :=
  cs.enemies.filter fun c => c.isAlive && c.isHittableFlag

def allocInstanceId (cs : CombatState) : Nat × CombatState :=
  (cs.nextInstanceId, { cs with nextInstanceId := cs.nextInstanceId + 1 })

def recordHistory (cs : CombatState) (entry : CombatHistoryEntry) : CombatState :=
  { cs with history := cs.history ++ [entry] }

end CombatState

/-- Out-of-combat run state. Ref: `Core.Runs/RunState.cs`. -/
structure RunState where
  runSeed          : UInt64 := 0
  currentActIndex  : Nat := 0
  ascensionLevel   : Nat := 0
  players          : List Player := []
  modifiers        : List ModelId := []
  badges           : List ModelId := []
  runModels        : List ModelId := []
  dominion         : Option ModelId := none
  currentRoom      : RoomType := .unassigned
  rngSet           : RunRngSet := RunRngSet.ofSeed 0
  rarityOddsOffset : Dec := Dec.ofScaled (-5) 2
  gold             : Nat := 99
  totalFloors      : Nat := 0
  deriving Repr, DecidableEq, Inhabited

end Sts2Model.Model
