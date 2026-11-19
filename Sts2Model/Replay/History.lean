/-
  Complete 18-kind CombatHistory schema, 9-kind RunHistory schema,
  and fine-grained per-hit DamageAttribution records for post-mortem timeline inspection.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Combat.History/CombatHistory.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Combat.History.Entries/*.cs` (18 entry classes)
  - `reference/sts2/MegaCrit.Sts2.Core.Runs.History/*.cs` (9 entry types)
-/
import Sts2Model.Core.Dec
import Sts2Model.Core.Ids
import Sts2Model.Core.Enums
import Sts2Model.Model.Creature
import Sts2Model.Model.Card

namespace Sts2Model.Replay

open Sts2Model.Core
open Sts2Model.Model

/-- All 18 semantic combat history entries matching `Core.Combat.History.Entries/*.cs`. -/
inductive CombatHistoryEntryEx where
  | arrowShot (round : Nat) (side : CombatSide) (playerId : PlayerId) (slotIdx : Nat)
  | blockGained (round : Nat) (side : CombatSide) (receiverId : CreatureId) (amount : Int) (props : ValueProp) (cardId : Option CardInstanceId)
  | cardAfflicted (round : Nat) (side : CombatSide) (playerId : PlayerId) (cardId : CardInstanceId) (afflictionId : ModelId)
  | cardDiscarded (round : Nat) (side : CombatSide) (playerId : PlayerId) (cardId : CardInstanceId)
  | cardDrawn (round : Nat) (side : CombatSide) (playerId : PlayerId) (cardId : CardInstanceId) (fromHandDraw : Bool)
  | cardExhausted (round : Nat) (side : CombatSide) (playerId : PlayerId) (cardId : CardInstanceId)
  | cardGenerated (round : Nat) (side : CombatSide) (playerId : PlayerId) (cardId : CardInstanceId) (creatorId : Option PlayerId)
  | cardPlayFinished (round : Nat) (side : CombatSide) (play : CardPlay) (wasEthereal : Bool)
  | cardPlayStarted (round : Nat) (side : CombatSide) (play : CardPlay)
  | creatureAttacked (round : Nat) (side : CombatSide) (attackerId : CreatureId) (results : List DamageResult)
  | damageReceived (round : Nat) (side : CombatSide) (receiverId : CreatureId) (dealerId : Option CreatureId) (cardModelId : Option ModelId) (result : DamageResult)
  | energySpent (round : Nat) (side : CombatSide) (playerId : PlayerId) (amount : Nat)
  | monsterPerformedMove (round : Nat) (side : CombatSide) (monsterId : CreatureId) (monsterModel : ModelId) (moveId : String) (targets : List CreatureId)
  | orbChanneled (round : Nat) (side : CombatSide) (playerId : PlayerId) (orbKind : OrbKind)
  | potionUsed (round : Nat) (side : CombatSide) (playerId : PlayerId) (potionId : ModelId) (targetId : Option CreatureId)
  | powerReceived (round : Nat) (side : CombatSide) (powerId : ModelId) (targetId : CreatureId) (applierId : Option CreatureId) (amount : Int)
  | starsModified (round : Nat) (side : CombatSide) (playerId : PlayerId) (delta : Int)
  | summoned (round : Nat) (side : CombatSide) (playerId : PlayerId) (amount : Int)
  deriving Repr, DecidableEq

/-- All 9 out-of-combat run history entry types matching `Core.Runs.History/*.cs`. -/
inductive RunHistoryEntryEx where
  | ancientChoice (actIndex floor : Nat) (playerId : PlayerId) (choiceKey : String) (wasChosen : Bool)
  | blitzMerchant (actIndex floor : Nat) (playerId : PlayerId) (modelId : Option ModelId) (wasPicked : Bool)
  | cardChoice (actIndex floor : Nat) (playerId : PlayerId) (cardId : ModelId) (wasPicked : Bool)
  | cardEnchantment (actIndex floor : Nat) (playerId : PlayerId) (cardId : ModelId) (enchantmentId : ModelId)
  | cardTransformation (actIndex floor : Nat) (playerId : PlayerId) (originalCard : ModelId) (finalCard : ModelId)
  | eventOption (actIndex floor : Nat) (playerId : PlayerId) (optionKey : String)
  | mapPoint (actIndex floor : Nat) (pointType : MapPointType) (roomCount : Nat)
  | mapPointRoom (actIndex floor : Nat) (roomType : RoomType) (modelId : Option ModelId) (monsterIds : List ModelId)
  | modelChoice (actIndex floor : Nat) (playerId : PlayerId) (choiceId : ModelId) (wasPicked : Bool)
  deriving Repr, DecidableEq

def CombatHistoryEntryEx.kindName : CombatHistoryEntryEx → String
  | .arrowShot ..            => "ArrowShot"
  | .blockGained ..          => "BlockGained"
  | .cardAfflicted ..        => "CardAfflicted"
  | .cardDiscarded ..        => "CardDiscarded"
  | .cardDrawn ..            => "CardDrawn"
  | .cardExhausted ..        => "CardExhausted"
  | .cardGenerated ..        => "CardGenerated"
  | .cardPlayFinished ..     => "CardPlayFinished"
  | .cardPlayStarted ..      => "CardPlayStarted"
  | .creatureAttacked ..     => "CreatureAttacked"
  | .damageReceived ..       => "DamageReceived"
  | .energySpent ..          => "EnergySpent"
  | .monsterPerformedMove .. => "MonsterPerformedMove"
  | .orbChanneled ..         => "OrbChanneled"
  | .potionUsed ..           => "PotionUsed"
  | .powerReceived ..        => "PowerReceived"
  | .starsModified ..        => "StarsModified"
  | .summoned ..             => "Summoned"

def allCombatHistoryKindNames : List String :=
  [ "ArrowShot", "BlockGained", "CardAfflicted", "CardDiscarded", "CardDrawn"
  , "CardExhausted", "CardGenerated", "CardPlayFinished", "CardPlayStarted"
  , "CreatureAttacked", "DamageReceived", "EnergySpent", "MonsterPerformedMove"
  , "OrbChanneled", "PotionUsed", "PowerReceived", "StarsModified", "Summoned" ]

def allRunHistoryKindNames : List String :=
  [ "AncientChoice", "BlitzMerchant", "CardChoice", "CardEnchantment"
  , "CardTransformation", "EventOption", "MapPoint", "MapPointRoom", "ModelChoice" ]

theorem combatHistoryKindCount : allCombatHistoryKindNames.length = 18 := rfl
theorem runHistoryKindCount : allRunHistoryKindNames.length = 9 := rfl

/-- Generic timeline-indexed wrapper attaching the event sequence index (`stepIdx`)
    to any semantic combat history entry, enabling arbitrary downstream causal queries
    without embedding analysis-specific fields into core simulation state. -/
structure TimedCombatHistoryEntry where
  stepIdx : Nat
  entry   : CombatHistoryEntryEx
  deriving Repr, DecidableEq

/-- Step-level causal damage attribution snapshot captured before/after each hit,
    enabling post-mortem queries (e.g. missed Vulnerable/Weak/Strength impact). -/
structure DamageAttribution where
  round            : Nat
  stepIdx          : Nat
  dealerId         : Option CreatureId
  targetId         : CreatureId
  cardModelId      : Option ModelId
  baseDamage       : Dec
  props            : ValueProp
  dealerStrength   : Int
  dealerWeak       : Bool
  targetVulnerable : Bool
  paperPhrog       : Bool
  modifiedDamage   : Dec
  blockedDamage    : Nat
  unblockedDamage  : Nat
  overkillDamage   : Nat
  targetHpBefore   : Nat
  targetHpAfter    : Nat
  deriving Repr, DecidableEq, Inhabited

end Sts2Model.Replay
