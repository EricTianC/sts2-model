/-
  Core enums, bitflags, and constants transcribed directly from `reference/sts2/`.
  Every constructor and flag value matches its C# counterpart.
-/

namespace Sts2Model.Core

-- ============================================================================
-- ValueProp & DamageProps / BlockProps
-- Ref: `Core.ValueProps/ValueProp.cs`, `ValuePropExtensions.cs`,
--      `DamageProps.cs`, `BlockProps.cs`
-- ============================================================================

/-- Damage and Block value properties bitflags.
    Ref: `Core.ValueProps/ValueProp.cs`. -/
structure ValueProp where
  unblockable  : Bool := false  -- bit 2
  unpowered    : Bool := false  -- bit 4
  move         : Bool := false  -- bit 8
  skipHurtAnim : Bool := false  -- bit 0x10
  fromArrow    : Bool := false  -- bit 0x20
  deriving Repr, DecidableEq, Inhabited

namespace ValueProp

def none : ValueProp := {}

def toBitmask (p : ValueProp) : Nat :=
  (if p.unblockable then 2 else 0) +
  (if p.unpowered then 4 else 0) +
  (if p.move then 8 else 0) +
  (if p.skipHurtAnim then 16 else 0) +
  (if p.fromArrow then 32 else 0)

def ofBitmask (m : Nat) : ValueProp :=
  { unblockable  := (m &&& 2) != 0
  , unpowered    := (m &&& 4) != 0
  , move         := (m &&& 8) != 0
  , skipHurtAnim := (m &&& 16) != 0
  , fromArrow    := (m &&& 32) != 0 }

/-- Ref: `ValuePropExtensions.IsPoweredAttack`. -/
@[inline] def isPoweredAttack (p : ValueProp) : Bool :=
  p.move && !p.unpowered

/-- Ref: `ValuePropExtensions.IsPoweredCardOrMonsterMoveBlock`. -/
@[inline] def isPoweredCardOrMonsterMoveBlock (p : ValueProp) : Bool :=
  p.move && !p.unpowered

/-- Ref: `ValuePropExtensions.IsCardOrMonsterMove`. -/
@[inline] def isCardOrMonsterMove (p : ValueProp) : Bool :=
  p.move

end ValueProp

namespace DamageProps
def card : ValueProp := { move := true }
def cardUnpowered : ValueProp := { unpowered := true, move := true }
def cardHpLoss : ValueProp := { unblockable := true, unpowered := true, move := true }
def monsterMove : ValueProp := { move := true }
def nonCardUnpowered : ValueProp := { unpowered := true }
def nonCardHpLoss : ValueProp := { unblockable := true, unpowered := true }
end DamageProps

namespace BlockProps
def card : ValueProp := { move := true }
def cardUnpowered : ValueProp := { unpowered := true, move := true }
def monsterMove : ValueProp := { move := true }
def nonCardUnpowered : ValueProp := { unpowered := true }
end BlockProps

-- ============================================================================
-- Hook phase / type flags
-- Ref: `Core.Hooks/HpLossHookPhase.cs`, `Core.Hooks/ModifyDamageHookType.cs`
-- ============================================================================

structure HpLossHookPhase where
  beforeWuppy : Bool := false  -- 1
  beforeOsty  : Bool := false  -- 2
  afterOsty   : Bool := false  -- 4
  deriving Repr, DecidableEq, Inhabited

namespace HpLossHookPhase
def none : HpLossHookPhase := {}
def wuppyOnly : HpLossHookPhase := { beforeWuppy := true }
def beforeOstyOnly : HpLossHookPhase := { beforeOsty := true }
def afterOstyOnly : HpLossHookPhase := { afterOsty := true }
def all : HpLossHookPhase := { beforeWuppy := true, beforeOsty := true, afterOsty := true }
end HpLossHookPhase

structure ModifyDamageHookType where
  additive       : Bool := false  -- 2
  multiplicative : Bool := false  -- 4
  cap            : Bool := false  -- 8
  deriving Repr, DecidableEq, Inhabited

namespace ModifyDamageHookType
def none : ModifyDamageHookType := {}
def capOnly : ModifyDamageHookType := { cap := true }
def all : ModifyDamageHookType := { additive := true, multiplicative := true, cap := true }
end ModifyDamageHookType

-- ============================================================================
-- Combat enums
-- Ref: `Core.Combat/CombatSide.cs`, `PlayerTurnPhase.cs`
-- ============================================================================

inductive CombatSide where
  | none
  | player
  | enemy
  deriving Repr, DecidableEq, Inhabited

def CombatSide.opponent : CombatSide → CombatSide
  | .player => .enemy
  | .enemy  => .player
  | .none   => .none

inductive PlayerTurnPhase where
  | none
  | start
  | autoPrePlay
  | play
  | autoPostPlay
  | «end»
  deriving Repr, DecidableEq, Inhabited

-- ============================================================================
-- Card enums
-- Ref: `Core.Entities.Cards/*.cs`
-- ============================================================================

inductive PileType where
  | none
  | draw
  | hand
  | discard
  | exhaust
  | play
  | deck
  deriving Repr, DecidableEq, Inhabited, Hashable

def PileType.isCombatPile : PileType → Bool
  | .draw | .hand | .discard | .exhaust | .play => true
  | .none | .deck => false

inductive CardPilePosition where
  | none
  | bottom
  | top
  | random
  deriving Repr, DecidableEq, Inhabited

inductive CardType where
  | none
  | attack
  | skill
  | power
  | status
  | curse
  | quest
  deriving Repr, DecidableEq, Inhabited

inductive CardRarity where
  | none
  | basic
  | common
  | uncommon
  | rare
  | ancient
  | event
  | token
  | status
  | curse
  | quest
  deriving Repr, DecidableEq, Inhabited

inductive CardKeyword where
  | none
  | exhaust
  | ethereal
  | innate
  | unplayable
  | retain
  | sly
  | eternal
  deriving Repr, DecidableEq, Inhabited

inductive CardTag where
  | none
  | strike
  | defend
  | minion
  | ostyAttack
  | shiv
  | wah
  | cho
  | ki
  | shoot
  deriving Repr, DecidableEq, Inhabited

inductive TargetType where
  | none
  | self
  | anyEnemy
  | allEnemies
  | randomEnemy
  | anyPlayer
  | anyAlly
  | allAllies
  | targetedNoCreature
  | osty
  deriving Repr, DecidableEq, Inhabited

inductive AutoPlayType where
  | none
  | default
  | slyDiscard
  deriving Repr, DecidableEq, Inhabited

inductive OrbEvokeType where
  | none
  | front
  | all
  deriving Repr, DecidableEq, Inhabited

inductive LocalCostType where
  | none
  | absolute
  | relative
  deriving Repr, DecidableEq, Inhabited

structure LocalCostModifierExpiration where
  endOfTurn  : Bool := false  -- 2
  whenPlayed : Bool := false  -- 4
  deriving Repr, DecidableEq, Inhabited

namespace LocalCostModifierExpiration
def endOfCombat : LocalCostModifierExpiration := {}
def onlyEndOfTurn : LocalCostModifierExpiration := { endOfTurn := true }
def onlyWhenPlayed : LocalCostModifierExpiration := { whenPlayed := true }
def endOfTurnOrWhenPlayed : LocalCostModifierExpiration := { endOfTurn := true, whenPlayed := true }
end LocalCostModifierExpiration

structure CostModifiers where
  includeLocal  : Bool := false  -- 2
  includeGlobal : Bool := false  -- 4
  deriving Repr, DecidableEq, Inhabited

namespace CostModifiers
def none : CostModifiers := {}
def localOnly : CostModifiers := { includeLocal := true }
def globalOnly : CostModifiers := { includeGlobal := true }
def all : CostModifiers := { includeLocal := true, includeGlobal := true }
end CostModifiers

structure UnplayableReason where
  hasUnplayableKeyword : Bool := false  -- 0x02
  blockedByHook        : Bool := false  -- 0x04
  blockedByCardLogic   : Bool := false  -- 0x08
  energyCostTooHigh    : Bool := false  -- 0x10
  starCostTooHigh      : Bool := false  -- 0x20
  noLivingAllies       : Bool := false  -- 0x40
  deriving Repr, DecidableEq, Inhabited

def UnplayableReason.none : UnplayableReason := {}

def UnplayableReason.isPlayable (r : UnplayableReason) : Bool :=
  r == UnplayableReason.none

-- ============================================================================
-- Power / Relic / Room / Map / Orb / FoolArrow enums
-- ============================================================================

inductive PowerType where
  | none
  | buff
  | debuff
  deriving Repr, DecidableEq, Inhabited

inductive PowerStackType where
  | none
  | counter
  | single
  deriving Repr, DecidableEq, Inhabited

inductive PowerInstanceType where
  | none
  | instanced
  | instancedPerApplier
  deriving Repr, DecidableEq, Inhabited

inductive RelicRarity where
  | none
  | starter
  | common
  | uncommon
  | rare
  | shop
  | event
  | ancient
  deriving Repr, DecidableEq, Inhabited

inductive RoomType where
  | unassigned
  | monster
  | elite
  | boss
  | treasure
  | shop
  | event
  | restSite
  | map
  deriving Repr, DecidableEq, Inhabited

inductive MapPointType where
  | unassigned
  | unknown
  | shop
  | treasure
  | restSite
  | monster
  | elite
  | boss
  | ancient
  deriving Repr, DecidableEq, Inhabited

inductive OrbKind where
  | lightning
  | frost
  | dark
  | plasma
  | glass
  | custom (id : String)
  deriving Repr, DecidableEq, Inhabited

inductive ArrowStatus where
  | retrieved
  | away
  | destroyed
  deriving Repr, DecidableEq, Inhabited

inductive CardRarityOddsType where
  | none
  | regularEncounter
  | eliteEncounter
  | bossEncounter
  | shop
  | uniform
  | blitz
  | blitzNeow
  deriving Repr, DecidableEq, Inhabited

/-- Run ascension level enum matching `Core.Entities.Ascension/AscensionLevel.cs`. -/
inductive AscensionLevel where
  | none
  | swarmingElites
  | wearyTraveler
  | poverty
  | tightBelt
  | ascendersBane
  | inflation
  | scarcity
  | toughEnemies
  | deadlyEnemies
  | doubleBoss
  deriving Repr, DecidableEq, Inhabited

def AscensionLevel.toNat : AscensionLevel → Nat
  | .none           => 0
  | .swarmingElites => 1
  | .wearyTraveler  => 2
  | .poverty        => 3
  | .tightBelt      => 4
  | .ascendersBane  => 5
  | .inflation      => 6
  | .scarcity       => 7
  | .toughEnemies   => 8
  | .deadlyEnemies  => 9
  | .doubleBoss     => 10

/-- Ascension-scaled integer value (`AscensionHelper.GetValueIfAscension`). -/
structure AscensionVal where
  threshold : Nat := 0
  ascVal    : Int
  baseVal   : Int
  deriving Repr, DecidableEq, Inhabited

namespace AscensionVal

def const (x : Int) : AscensionVal :=
  ⟨0, x, x⟩

def eval (v : AscensionVal) (asc : Nat) : Int :=
  if asc ≥ v.threshold then v.ascVal else v.baseVal

end AscensionVal

end Sts2Model.Core
