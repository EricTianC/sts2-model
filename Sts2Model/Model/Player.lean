/-
  Player, PlayerCombatState, RelicInstance, PotionInstance, and ArrowSlot models.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Players/Player.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Players/PlayerCombatState.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.FoolArrows/ArrowSlot.cs`
-/
import Sts2Model.Core.Dec
import Sts2Model.Core.Ids
import Sts2Model.Core.Enums
import Sts2Model.Model.Card
import Sts2Model.Model.Orb

namespace Sts2Model.Model

open Sts2Model.Core

/-- Mutable relic instance owned by a player. Ref: `Core.Models/RelicModel.cs`. -/
structure RelicInstance where
  modelId  : ModelId
  rarity   : RelicRarity := .common
  isMelted : Bool := false
  counter  : Int := -1
  deriving Repr, DecidableEq, Inhabited

/-- Mutable potion instance in a player's potion slot. Ref: `Core.Models/PotionModel.cs`. -/
structure PotionInstance where
  modelId : ModelId
  deriving Repr, DecidableEq, Inhabited

/-- Fool character arrow slot. Ref: `Core.Entities.FoolArrows/ArrowSlot.cs`. -/
structure ArrowSlot where
  status             : ArrowStatus := .retrieved
  destroyAfterImpaled : Bool := false
  deriving Repr, DecidableEq, Inhabited

def ArrowSlot.isAvailable (a : ArrowSlot) : Bool :=
  a.status == .retrieved

/-- Per-combat player state. Ref: `Core.Entities.Players/PlayerCombatState.cs`. -/
structure PlayerCombatState where
  turnNumber          : Nat := 1
  phase               : PlayerTurnPhase := .none
  energy              : Nat := 0
  baseMaxEnergy       : Nat := 3
  stars               : Nat := 0
  piles               : PlayerPiles := {}
  orbQueue            : OrbQueue := {}
  arrows              : List ArrowSlot := []
  petIds              : List CreatureId := []
  sovereignBladeForged : Bool := false
  sovereignBladeBonus : Dec := Dec.zero
  playedTagsThisTurn  : List CardTag := []
  deriving Repr, DecidableEq, Inhabited

namespace PlayerCombatState

def availableArrowCount (pcs : PlayerCombatState) : Nat :=
  (pcs.arrows.filter ArrowSlot.isAvailable).length

def gainArrow (pcs : PlayerCombatState) : PlayerCombatState :=
  { pcs with arrows := pcs.arrows ++ [{}] }

def gainEnergy (pcs : PlayerCombatState) (amount : Nat) : PlayerCombatState :=
  { pcs with energy := min 999999999 (pcs.energy + amount) }

def loseEnergy (pcs : PlayerCombatState) (amount : Nat) : PlayerCombatState :=
  { pcs with energy := pcs.energy - min pcs.energy amount }

def gainStars (pcs : PlayerCombatState) (amount : Nat) : PlayerCombatState :=
  { pcs with stars := pcs.stars + amount }

def loseStars (pcs : PlayerCombatState) (amount : Nat) : PlayerCombatState :=
  { pcs with stars := pcs.stars - min pcs.stars amount }

/-- Compute `(energyRequired, starsRequired, UnplayableReason)` for a card,
    including `ShouldPayExcessEnergyCostWithStars` (1 missing energy = 2 stars).
    Ref: `PlayerCombatState.HasEnoughResourcesFor`. -/
def checkResourcesFor (pcs : PlayerCombatState) (energyCost starsCost : Int)
    (payExcessWithStars : Bool := false) : Nat × Nat × UnplayableReason :=
  let e0 := Int.toNat (max 0 energyCost)
  let s0 := Int.toNat (max 0 starsCost)
  let (eReq, sReq) :=
    if e0 > pcs.energy && payExcessWithStars then
      (pcs.energy, s0 + (e0 - pcs.energy) * 2)
    else
      (e0, s0)
  let r : UnplayableReason :=
    { energyCostTooHigh := eReq > pcs.energy
    , starCostTooHigh   := sReq > pcs.stars }
  (eReq, sReq, r)

end PlayerCombatState

/-- Run-level player state, keeping out-of-combat `deck` separate from `combatState`.
    Ref: `Core.Entities.Players/Player.cs`. -/
structure Player where
  playerId        : PlayerId
  creatureId      : CreatureId
  characterId     : ModelId
  isActiveForHooks : Bool := true
  deck            : List CardInstance := []
  relics          : List RelicInstance := []
  potions         : List (Option PotionInstance) := []
  baseMaxEnergy   : Nat := 3
  baseOrbSlots    : Nat := 0
  baseArrowSlots  : Nat := 0
  combatState     : Option PlayerCombatState := none
  deriving Repr, DecidableEq, Inhabited

end Sts2Model.Model
