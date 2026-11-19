/-
  Creature entity, DamageResult, SummonResult, and low-level internal state transitions.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Creatures/Creature.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Creatures/DamageResult.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Creatures/SummonResult.cs`
-/
import Sts2Model.Core.Dec
import Sts2Model.Core.Ids
import Sts2Model.Core.Enums
import Sts2Model.Model.Power

namespace Sts2Model.Model

open Sts2Model.Core

/-- Metadata about a single damage application to a creature.
    Ref: `Core.Entities.Creatures/DamageResult.cs`. -/
structure DamageResult where
  receiverId      : CreatureId
  originalTargetId : CreatureId
  props           : ValueProp
  intendedHpLoss  : Int := 0
  blockedDamage   : Nat := 0
  unblockedDamage : Nat := 0
  overkillDamage  : Nat := 0
  wasBlockBroken  : Bool := false
  wasFullyBlocked : Bool := false
  wasTargetKilled : Bool := false
  deriving Repr, DecidableEq, Inhabited

def DamageResult.totalDamage (r : DamageResult) : Nat :=
  r.blockedDamage + r.unblockedDamage

/-- Metadata about summoning a pet (e.g. Osty).
    Ref: `Core.Entities.Creatures/SummonResult.cs`. -/
structure SummonResult where
  creatureId : Option CreatureId
  amount     : Dec
  deriving Repr, DecidableEq, Inhabited

/-- Monster AI state descriptor attached to enemy creatures. -/
structure MonsterInfo where
  modelId          : ModelId
  currentMoveId    : String := ""
  nextMoveId       : String := ""
  stateLog         : List String := []
  spawnedThisTurn  : Bool := false
  shouldDisappearFromDoom : Bool := true
  deriving Repr, DecidableEq, Inhabited

/-- Combat creature (either a Player's Creature, a Pet, or an Enemy Monster).
    Ref: `Core.Entities.Creatures/Creature.cs`. -/
structure Creature where
  id           : CreatureId
  modelId      : ModelId
  side         : CombatSide
  playerId     : Option PlayerId := none
  petOwnerId   : Option PlayerId := none
  currentHp    : Nat
  maxHp        : Nat
  block        : Nat := 0
  powers       : List PowerInstance := []
  monster      : Option MonsterInfo := none
  isHittableFlag : Bool := true
  deriving Repr, DecidableEq, Inhabited

namespace Creature

def statCap : Nat := 999999999

def isAlive (c : Creature) : Bool := c.currentHp > 0
def isDead (c : Creature) : Bool := !c.isAlive
def isPlayer (c : Creature) : Bool := c.playerId.isSome
def isMonster (c : Creature) : Bool := c.monster.isSome
def isPet (c : Creature) : Bool := c.petOwnerId.isSome

def isSecondaryEnemy (c : Creature) : Bool :=
  c.side == .enemy && c.powers.any (·.ownerIsSecondaryEnemy)

def isPrimaryEnemy (c : Creature) : Bool :=
  c.side == .enemy && !c.isSecondaryEnemy

def isStunned (c : Creature) : Bool :=
  match c.monster with
  | some m => m.nextMoveId == "STUNNED"
  | none   => false

def getPower (c : Creature) (mid : ModelId) : Option PowerInstance :=
  c.powers.find? (·.modelId == mid)

def getPowerInstances (c : Creature) (mid : ModelId) : List PowerInstance :=
  c.powers.filter (·.modelId == mid)

def getPowerAmount (c : Creature) (mid : ModelId) : Int :=
  (c.getPower mid).map (·.amount) |>.getD 0

def hasPower (c : Creature) (mid : ModelId) : Bool :=
  c.powers.any (·.modelId == mid)

/-- Ref: `Creature.DamageBlockInternal(decimal amount, ValueProp props)`.
    Returns `(updatedCreature, blockedAmountDec)`. -/
def damageBlockInternal (c : Creature) (amount : Dec) (props : ValueProp) : Creature × Dec :=
  let blocked : Dec :=
    if props.unblockable then
      Dec.zero
    else
      Dec.min (Dec.ofNat c.block) amount
  let blockedTrunc := Int.toNat (max 0 blocked.truncate)
  let newBlock := c.block - min c.block blockedTrunc
  ({ c with block := newBlock }, blocked)

/-- Ref: `Creature.LoseHpInternal(decimal amount, ValueProp props)`.
    Returns `(updatedCreature, damageResult)`. -/
def loseHpInternal (c : Creature) (amount : Dec) (props : ValueProp) : Creature × DamageResult :=
  let killed := c.currentHp > 0 && Dec.ofNat c.currentHp ≤ amount
  let clampedAmt := Dec.clamp amount Dec.zero (Dec.ofNat statCap)
  let hpLoss : Nat := Int.toNat (max 0 clampedAmt.truncate)
  let prevHp := c.currentHp
  let newHp := prevHp - min prevHp hpLoss
  let unblocked := prevHp - newHp
  let overkill := if killed then hpLoss - min hpLoss prevHp else 0
  let res : DamageResult :=
    { receiverId := c.id
    , originalTargetId := c.id
    , props := props
    , unblockedDamage := unblocked
    , wasTargetKilled := killed
    , overkillDamage := overkill }
  ({ c with currentHp := newHp }, res)

/-- Ref: `Creature.GainBlockInternal(decimal amount)`. -/
def gainBlockInternal (c : Creature) (amount : Dec) : Creature :=
  if amount < Dec.zero then c
  else
    let sumDec := Dec.add (Dec.ofNat c.block) amount
    let capped := Dec.min sumDec (Dec.ofNat statCap)
    { c with block := capped.toNat }

/-- Ref: `Creature.LoseBlockInternal(decimal amount)`. -/
def loseBlockInternal (c : Creature) (amount : Dec) : Creature :=
  if amount < Dec.zero then c
  else
    let diffDec := Dec.sub (Dec.ofNat c.block) amount
    { c with block := diffDec.toNat }

/-- Ref: `Creature.SetCurrentHpInternal` and `Creature.HealInternal`. -/
def healInternal (c : Creature) (amount : Dec) : Creature :=
  let target := Dec.min (Dec.add (Dec.ofNat c.currentHp) amount) (Dec.ofNat c.maxHp)
  { c with currentHp := target.toNat }

/-- Ref: `Creature.SetMaxHpInternal(decimal amount)`. -/
def setMaxHpInternal (c : Creature) (amount : Dec) : Creature :=
  if amount < Dec.zero then c
  else
    let newMax := min amount.toNat statCap
    { c with maxHp := newMax, currentHp := min c.currentHp newMax }

end Creature
end Sts2Model.Model
