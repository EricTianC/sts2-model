/-
  Tier-1 handcrafted core Powers, Potions, Cards, and Monster AI blueprints
  plus layered `fullVanillaEffectEnv` combining Tier-1 > Tier-2 (Roslyn AST) > generic fallback.
-/
import Sts2Model.Sim.EffectIR
import Sts2Model.Sim.Generated.Verify
import Sts2Model.Mechanics.Necrobinder

namespace Sts2Model.Sim

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook
open Sts2Model.Combat
open Sts2Model.Mechanics
open Sts2Model.Sim.Generated

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

def mkThornsPower (amt : Int) (ownerId : CreatureId := 0) : PowerInstance :=
  { instanceId := 0, modelId := ModelId.mkPower "THORNS_POWER", ownerId := ownerId
  , powerType := .buff, stackType := .counter, allowNegative := false, amount := amt }

def mkPlatingPower (amt : Int) (ownerId : CreatureId := 0) : PowerInstance :=
  { instanceId := 0, modelId := ModelId.mkPower "PLATING_POWER", ownerId := ownerId
  , powerType := .buff, stackType := .counter, allowNegative := false, amount := amt }

def mkRitualPower (amt : Int) (ownerId : CreatureId := 0) : PowerInstance :=
  { instanceId := 0, modelId := ModelId.mkPower "RITUAL_POWER", ownerId := ownerId
  , powerType := .buff, stackType := .counter, allowNegative := false, amount := amt }

/-- Behavior registry extending `builtinBehaviorRegistry` with Tier-1 character/mechanic hooks. -/
def tier1BehaviorRegistry (cs : CombatState) : BehaviorRegistry := fun mid =>
  if mid == dieForYouPowerModelId then dieForYouBehavior cs
  else builtinBehaviorRegistry cs mid

-- ============================================================================
-- Tier-1 Core Cards, Potions, and Monster AI Blueprints
-- ============================================================================

def genericCardFallback (card : CardInstance) : EffectProgram :=
  if card.cardType == .attack && Dec.zero < card.baseDamage then
    [.dealDamage .chosenTarget card.baseDamage]
  else if card.gainsBlock && Dec.zero < card.baseBlock then
    [.gainBlock .self card.baseBlock]
  else []

def tier1CardEffect? (card : CardInstance) : Option EffectProgram :=
  let upg := card.upgradeLevel > 0
  let dmgOr (d : Int) : Dec :=
    if Dec.eqVal card.baseDamage Dec.zero then Dec.ofInt d else card.baseDamage
  let blkOr (b : Int) : Dec :=
    if Dec.eqVal card.baseBlock Dec.zero then Dec.ofInt b else card.baseBlock
  match card.modelId.entry with
  | "STRIKE_IRONCLAD" | "STRIKE_SILENT" | "STRIKE_DEFECT" | "STRIKE_NECROBINDER" | "STRIKE_REGENT" =>
      some [.dealDamage .chosenTarget (dmgOr (if upg then 9 else 6))]
  | "DEFEND_IRONCLAD" | "DEFEND_SILENT" | "DEFEND_DEFECT" | "DEFEND_NECROBINDER" | "DEFEND_REGENT" =>
      some [.gainBlock .self (blkOr (if upg then 8 else 5))]
  | "BASH" =>
      some [ .dealDamage .chosenTarget (dmgOr (if upg then 10 else 8))
           , .applyPower .chosenTarget (mkVulnerablePower 1) (Dec.ofNat (if upg then 3 else 2)) ]
  | "TWIN_STRIKE" =>
      some [.dealDamage .chosenTarget (dmgOr (if upg then 7 else 5)) 2]
  | "ANGER" =>
      some [ .dealDamage .chosenTarget (dmgOr (if upg then 8 else 6))
           , .addCardToPile { card with instanceId := card.instanceId + 50000, isDupe := true } .discard ]
  | "POMMEL_STRIKE" =>
      some [ .dealDamage .chosenTarget (dmgOr (if upg then 10 else 9))
           , .draw (if upg then 2 else 1) ]
  | "IRON_WAVE" =>
      some [ .gainBlock .self (blkOr (if upg then 7 else 5))
           , .dealDamage .chosenTarget (dmgOr (if upg then 7 else 5)) ]
  | "CLEAVE" =>
      some [.dealDamage .allEnemies (dmgOr (if upg then 11 else 8))]
  | "CLOTHESLINE" =>
      some [ .dealDamage .chosenTarget (dmgOr (if upg then 14 else 12))
           , .applyPower .chosenTarget (mkWeakPower 1) (Dec.ofNat (if upg then 3 else 2)) ]
  | "UPPERCUT" =>
      let amt := Dec.ofNat (if upg then 2 else 1)
      some [ .dealDamage .chosenTarget (dmgOr 13)
           , .applyPower .chosenTarget (mkWeakPower 1) amt
           , .applyPower .chosenTarget (mkVulnerablePower 1) amt ]
  | "SHOCKWAVE" =>
      let amt := Dec.ofNat (if upg then 5 else 3)
      some [ .applyPower .allEnemies (mkWeakPower 1) amt
           , .applyPower .allEnemies (mkVulnerablePower 1) amt ]
  | "BLUDGEON" =>
      some [.dealDamage .chosenTarget (dmgOr (if upg then 42 else 32))]
  | "INFLAME" =>
      some [.applyPower .self (mkStrengthPower 1) (Dec.ofNat (if upg then 3 else 2))]
  | "FOOTWORK" =>
      some [.applyPower .self (mkDexterityPower 1) (Dec.ofNat (if upg then 3 else 2))]
  | "NEUTRALIZE" =>
      some [ .dealDamage .chosenTarget (dmgOr (if upg then 4 else 3))
           , .applyPower .chosenTarget (mkWeakPower 1) (Dec.ofNat (if upg then 2 else 1)) ]
  | "SURVIVOR" =>
      some [ .gainBlock .self (blkOr (if upg then 11 else 8))
           , .discardFromHand 1 ]
  | "SHRUG_IT_OFF" =>
      some [ .gainBlock .self (blkOr (if upg then 11 else 8))
           , .draw 1 ]
  | "POISONED_STAB" =>
      some [ .dealDamage .chosenTarget (dmgOr (if upg then 8 else 6))
           , .applyPower .chosenTarget (mkPoisonPower 1) (Dec.ofNat (if upg then 4 else 3)) ]
  | "ZAP" =>
      some [.channelOrb .lightning]
  | "DUALCAST" =>
      some [.evokeOrb 2]
  | "SOVEREIGN_BLADE" =>
      some [.dealDamage .chosenTarget (dmgOr 10)]
  | "STAR_STRIKE" =>
      some [.dealDamage .chosenTarget (dmgOr 14)]
  | _ => none

def vanillaCardEffect (card : CardInstance) : EffectProgram :=
  (tier1CardEffect? card).getD (genericCardFallback card)

def tier1PotionEffect? (potionId : ModelId) : Option EffectProgram :=
  match potionId.entry with
  | "FIRE_POTION"     => some [.dealDamage .chosenTarget (Dec.ofNat 20) 1 DamageProps.nonCardUnpowered]
  | "BLOCK_POTION"    => some [.gainBlock .self (Dec.ofNat 12) BlockProps.nonCardUnpowered]
  | "STRENGTH_POTION" => some [.applyPower .self (mkStrengthPower 1) (Dec.ofNat 2)]
  | "FEAR_POTION"     => some [.applyPower .chosenTarget (mkVulnerablePower 1) (Dec.ofNat 3)]
  | "WEAK_POTION"     => some [.applyPower .chosenTarget (mkWeakPower 1) (Dec.ofNat 3)]
  | "ENERGY_POTION"   => some [.gainEnergy 2]
  | "SWIFT_POTION"    => some [.draw 3]
  | "HEAL_POTION"     => some [.heal .self (Dec.ofNat 10)]
  | _                 => none

def vanillaPotionEffect (potionId : ModelId) : EffectProgram :=
  (tier1PotionEffect? potionId).getD []

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

/-- Default Tier-1 headless simulation environment (lightweight for kernel proofs). -/
def tier1EffectEnv : EffectEnv :=
  { behaviorReg := tier1BehaviorRegistry
  , cardEffect := vanillaCardEffect
  , potionEffect := vanillaPotionEffect
  , monsterBlueprint := vanillaMonsterBlueprint
  , knownCardEffect := tier1CardEffect?
  , knownPotionEffect := tier1PotionEffect? }

abbrev vanillaEffectEnv : EffectEnv := tier1EffectEnv

def knownVanillaCardEffect (card : CardInstance) : Option EffectProgram :=
  (tier1CardEffect? card).orElse fun _ => lookupGeneratedCard card.modelId.entry (card.upgradeLevel > 0)

def fullVanillaCardEffect (card : CardInstance) : EffectProgram :=
  (knownVanillaCardEffect card).getD (genericCardFallback card)

def knownVanillaPotionEffect (potionId : ModelId) : Option EffectProgram :=
  (tier1PotionEffect? potionId).orElse fun _ => lookupGeneratedPotion potionId.entry

def fullVanillaPotionEffect (potionId : ModelId) : EffectProgram :=
  (knownVanillaPotionEffect potionId).getD []

def fullVanillaMonsterBlueprint (mid : ModelId) : Option MonsterBlueprint :=
  match vanillaMonsterBlueprint mid with
  | some bp => some bp
  | none    => lookupGeneratedMonster mid.entry

/-- Layered full vanilla simulation environment (`Tier-1 > Tier-2 AST > generic fallback`). -/
def fullVanillaEffectEnv : EffectEnv :=
  { behaviorReg := tier1BehaviorRegistry
  , cardEffect := fullVanillaCardEffect
  , potionEffect := fullVanillaPotionEffect
  , monsterBlueprint := fullVanillaMonsterBlueprint
  , knownCardEffect := knownVanillaCardEffect
  , knownPotionEffect := knownVanillaPotionEffect }

end Sts2Model.Sim
