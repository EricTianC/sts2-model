/-
  Tier-1 handcrafted core Powers, Potions, Cards, and Monster AI blueprints
  for headless multiplayer simulation and counterfactual replay.
-/
import Sts2Model.Sim.EffectIR
import Sts2Model.Mechanics.Necrobinder

namespace Sts2Model.Sim

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook
open Sts2Model.Combat
open Sts2Model.Mechanics

-- ============================================================================
-- Tier-1 Canonical Power Templates
-- ============================================================================

def mkStrengthPower (amt : Int) (ownerId : CreatureId := 0) : PowerInstance :=
  { instanceId := 0, modelId := ModelId.mkPower "STRENGTH_POWER", ownerId := ownerId
  , powerType := .buff, stackType := .counter, allowNegative := true, amount := amt }

def mkDexterityPower (amt : Int) (ownerId : CreatureId := 0) : PowerInstance :=
  { instanceId := 0, modelId := ModelId.mkPower "DEXTERITY_POWER", ownerId := ownerId
  , powerType := .buff, stackType := .counter, allowNegative := true, amount := amt }

def mkVulnerablePower (amt : Int) (ownerId : CreatureId := 0) : PowerInstance :=
  { instanceId := 0, modelId := ModelId.mkPower "VULNERABLE_POWER", ownerId := ownerId
  , powerType := .debuff, stackType := .counter, allowNegative := false, amount := amt }

def mkWeakPower (amt : Int) (ownerId : CreatureId := 0) : PowerInstance :=
  { instanceId := 0, modelId := ModelId.mkPower "WEAK_POWER", ownerId := ownerId
  , powerType := .debuff, stackType := .counter, allowNegative := false, amount := amt }

def mkFrailPower (amt : Int) (ownerId : CreatureId := 0) : PowerInstance :=
  { instanceId := 0, modelId := ModelId.mkPower "FRAIL_POWER", ownerId := ownerId
  , powerType := .debuff, stackType := .counter, allowNegative := false, amount := amt }

def mkArtifactPower (amt : Int) (ownerId : CreatureId := 0) : PowerInstance :=
  { instanceId := 0, modelId := ModelId.mkPower "ARTIFACT_POWER", ownerId := ownerId
  , powerType := .buff, stackType := .counter, allowNegative := false, amount := amt }

def mkIntangiblePower (amt : Int) (ownerId : CreatureId := 0) : PowerInstance :=
  { instanceId := 0, modelId := ModelId.mkPower "INTANGIBLE_POWER", ownerId := ownerId
  , powerType := .buff, stackType := .counter, allowNegative := false, amount := amt }

def mkBarricadePower (ownerId : CreatureId := 0) : PowerInstance :=
  { instanceId := 0, modelId := ModelId.mkPower "BARRICADE_POWER", ownerId := ownerId
  , powerType := .buff, stackType := .single, allowNegative := false, amount := 1 }

def mkPoisonPower (amt : Int) (ownerId : CreatureId := 0) : PowerInstance :=
  { instanceId := 0, modelId := ModelId.mkPower "POISON_POWER", ownerId := ownerId
  , powerType := .debuff, stackType := .counter, allowNegative := false, amount := amt }

def mkFocusPower (amt : Int) (ownerId : CreatureId := 0) : PowerInstance :=
  { instanceId := 0, modelId := ModelId.mkPower "FOCUS_POWER", ownerId := ownerId
  , powerType := .buff, stackType := .counter, allowNegative := true, amount := amt }

def mkDoomPower (amt : Int) (ownerId : CreatureId := 0) : PowerInstance :=
  { instanceId := 0, modelId := ModelId.mkPower "DOOM_POWER", ownerId := ownerId
  , powerType := .debuff, stackType := .counter, allowNegative := false, amount := amt }

/-- Behavior registry extending `builtinBehaviorRegistry` with Tier-1 character/mechanic hooks. -/
def tier1BehaviorRegistry (cs : CombatState) : BehaviorRegistry := fun mid =>
  if mid == dieForYouPowerModelId then dieForYouBehavior cs
  else builtinBehaviorRegistry cs mid

-- ============================================================================
-- Tier-1 Core Cards, Potions, and Monster AI Blueprints
-- ============================================================================

def vanillaCardEffect (card : CardInstance) : EffectProgram :=
  let upg := card.upgradeLevel > 0
  let dmgOr (d : Int) : Dec :=
    if Dec.eqVal card.baseDamage Dec.zero then Dec.ofInt d else card.baseDamage
  let blkOr (b : Int) : Dec :=
    if Dec.eqVal card.baseBlock Dec.zero then Dec.ofInt b else card.baseBlock
  match card.modelId.entry with
  | "STRIKE_IRONCLAD" | "STRIKE_SILENT" | "STRIKE_DEFECT" | "STRIKE_NECROBINDER" | "STRIKE_REGENT" =>
      [.dealDamage .chosenTarget (dmgOr (if upg then 9 else 6))]
  | "DEFEND_IRONCLAD" | "DEFEND_SILENT" | "DEFEND_DEFECT" | "DEFEND_NECROBINDER" | "DEFEND_REGENT" =>
      [.gainBlock .self (blkOr (if upg then 8 else 5))]
  | "BASH" =>
      [ .dealDamage .chosenTarget (dmgOr (if upg then 10 else 8))
      , .applyPower .chosenTarget (mkVulnerablePower 1) (Dec.ofNat (if upg then 3 else 2)) ]
  | "TWIN_STRIKE" =>
      [.dealDamage .chosenTarget (dmgOr (if upg then 7 else 5)) 2]
  | "ANGER" =>
      [ .dealDamage .chosenTarget (dmgOr (if upg then 8 else 6))
      , .addCardToPile { card with instanceId := card.instanceId + 50000, isDupe := true } .discard ]
  | "POMMEL_STRIKE" =>
      [ .dealDamage .chosenTarget (dmgOr (if upg then 10 else 9))
      , .draw (if upg then 2 else 1) ]
  | "IRON_WAVE" =>
      [ .gainBlock .self (blkOr (if upg then 7 else 5))
      , .dealDamage .chosenTarget (dmgOr (if upg then 7 else 5)) ]
  | "CLEAVE" =>
      [.dealDamage .allEnemies (dmgOr (if upg then 11 else 8))]
  | "CLOTHESLINE" =>
      [ .dealDamage .chosenTarget (dmgOr (if upg then 14 else 12))
      , .applyPower .chosenTarget (mkWeakPower 1) (Dec.ofNat (if upg then 3 else 2)) ]
  | "UPPERCUT" =>
      let amt := Dec.ofNat (if upg then 2 else 1)
      [ .dealDamage .chosenTarget (dmgOr 13)
      , .applyPower .chosenTarget (mkWeakPower 1) amt
      , .applyPower .chosenTarget (mkVulnerablePower 1) amt ]
  | "SHOCKWAVE" =>
      let amt := Dec.ofNat (if upg then 5 else 3)
      [ .applyPower .allEnemies (mkWeakPower 1) amt
      , .applyPower .allEnemies (mkVulnerablePower 1) amt ]
  | "BLUDGEON" =>
      [.dealDamage .chosenTarget (dmgOr (if upg then 42 else 32))]
  | "INFLAME" =>
      [.applyPower .self (mkStrengthPower 1) (Dec.ofNat (if upg then 3 else 2))]
  | "FOOTWORK" =>
      [.applyPower .self (mkDexterityPower 1) (Dec.ofNat (if upg then 3 else 2))]
  | "NEUTRALIZE" =>
      [ .dealDamage .chosenTarget (dmgOr (if upg then 4 else 3))
      , .applyPower .chosenTarget (mkWeakPower 1) (Dec.ofNat (if upg then 2 else 1)) ]
  | "SURVIVOR" =>
      [ .gainBlock .self (blkOr (if upg then 11 else 8))
      , .discardChosen 0 1 ]
  | "SHRUG_IT_OFF" =>
      [ .gainBlock .self (blkOr (if upg then 11 else 8))
      , .draw 1 ]
  | "POISONED_STAB" =>
      [ .dealDamage .chosenTarget (dmgOr (if upg then 8 else 6))
      , .applyPower .chosenTarget (mkPoisonPower 1) (Dec.ofNat (if upg then 4 else 3)) ]
  | "ZAP" =>
      [.channelOrb .lightning]
  | "DUALCAST" =>
      [.evokeOrb 2]
  | "SOVEREIGN_BLADE" =>
      [.dealDamage .chosenTarget (dmgOr 10)]
  | "STAR_STRIKE" =>
      [.dealDamage .chosenTarget (dmgOr 14)]
  | _ =>
      if card.cardType == .attack && Dec.zero < card.baseDamage then
        [.dealDamage .chosenTarget card.baseDamage]
      else if card.gainsBlock && Dec.zero < card.baseBlock then
        [.gainBlock .self card.baseBlock]
      else []

def vanillaPotionEffect (potionId : ModelId) : EffectProgram :=
  match potionId.entry with
  | "FIRE_POTION"     => [.dealDamage .chosenTarget (Dec.ofNat 20) 1 DamageProps.nonCardUnpowered]
  | "BLOCK_POTION"    => [.gainBlock .self (Dec.ofNat 12) BlockProps.nonCardUnpowered]
  | "STRENGTH_POTION" => [.applyPower .self (mkStrengthPower 1) (Dec.ofNat 2)]
  | "FEAR_POTION"     => [.applyPower .chosenTarget (mkVulnerablePower 1) (Dec.ofNat 3)]
  | "WEAK_POTION"     => [.applyPower .chosenTarget (mkWeakPower 1) (Dec.ofNat 3)]
  | "ENERGY_POTION"   => [.gainEnergy 2]
  | "SWIFT_POTION"    => [.draw 3]
  | "HEAL_POTION"     => [.heal .self (Dec.ofNat 10)]
  | _                 => []

/-- Example 2-move alternating coop guardian monster blueprint using `MonsterAI`. -/
def coopGuardianBlueprint : MonsterBlueprint :=
  { modelId := ModelId.mkMonster "COOP_GUARDIAN"
  , stateMachine :=
      { initialStateId := "SLAM"
      , currentStateId := "SLAM"
      , nodes := fun sid =>
          match sid with
          | "SLAM" => some { id := "SLAM", kind := .move "FORTIFY" true false }
          | "FORTIFY" => some { id := "FORTIFY", kind := .move "SLAM" true false }
          | _ => none }
  , moveEffects := fun moveId =>
      match moveId with
      | "SLAM" => [.dealDamage .allAllies (Dec.ofNat 7) 1 DamageProps.monsterMove]
      | "FORTIFY" =>
          [ .gainBlock .self (Dec.ofNat 8) BlockProps.monsterMove
          , .applyPower .self (mkStrengthPower 1) (Dec.ofNat 1) ]
      | _ => [] }

/-- Example Cultist blueprint (incant Ritual / Strength on first turn, then Strike). -/
def cultistBlueprint : MonsterBlueprint :=
  { modelId := ModelId.mkMonster "CULTIST"
  , stateMachine :=
      { initialStateId := "INCANT"
      , currentStateId := "INCANT"
      , nodes := fun sid =>
          match sid with
          | "INCANT" => some { id := "INCANT", kind := .move "DARK_STRIKE" true true }
          | "DARK_STRIKE" => some { id := "DARK_STRIKE", kind := .move "DARK_STRIKE" true false }
          | _ => none }
  , moveEffects := fun moveId =>
      match moveId with
      | "INCANT" => [.applyPower .self (mkStrengthPower 1) (Dec.ofNat 3)]
      | "DARK_STRIKE" => [.dealDamage .firstLivingPlayer (Dec.ofNat 6) 1 DamageProps.monsterMove]
      | _ => [] }

def vanillaMonsterBlueprint (mid : ModelId) : Option MonsterBlueprint :=
  match mid.entry with
  | "COOP_GUARDIAN" => some coopGuardianBlueprint
  | "CULTIST"       => some cultistBlueprint
  | _               => none

/-- Default Tier-1 headless simulation environment. -/
def vanillaEffectEnv : EffectEnv :=
  { behaviorReg := tier1BehaviorRegistry
  , cardEffect := vanillaCardEffect
  , potionEffect := vanillaPotionEffect
  , monsterBlueprint := vanillaMonsterBlueprint }

end Sts2Model.Sim
