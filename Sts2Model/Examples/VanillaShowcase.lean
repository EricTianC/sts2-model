/-
  30 Executable Vanilla Mechanics Showcase Scenarios grounded directly in `reference/sts2/`.
  Covers Damage Pipeline, Block, Powers/Artifact, Cards/Piles/Costs, Turn State Machine,
  Monster AI, Defect Orbs, Necrobinder Osty/Doom, Regent Forge/Stars, Fool Arrows/Melodies,
  Dread Dominion, ActMap DAG, CardRarityOdds, and RelicGrabBag.
-/
import Sts2Model.Combat.TurnLoop
import Sts2Model.Combat.MonsterAI
import Sts2Model.Mechanics.Orbs
import Sts2Model.Mechanics.Necrobinder
import Sts2Model.Mechanics.Regent
import Sts2Model.Mechanics.Fool
import Sts2Model.Mechanics.Dread
import Sts2Model.Run.RunLoop
import Sts2Model.Catalog.Verify

namespace Sts2Model.Examples

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook
open Sts2Model.Command
open Sts2Model.Combat
open Sts2Model.Mechanics
open Sts2Model.Run
open Sts2Model.Catalog

-- Shared fixture constructors
private def mkTestPlayer (pid : PlayerId := 1) (cid : CreatureId := 100) (energy : Nat := 3)
    (stars : Nat := 0) (relics : List RelicInstance := []) : Player :=
  { playerId := pid
  , creatureId := cid
  , characterId := ModelId.mkCharacter "IRONCLAD"
  , relics := relics
  , baseMaxEnergy := energy
  , combatState := some
      { energy := energy
      , baseMaxEnergy := energy
      , stars := stars } }

private def mkPlayerCreature (id : CreatureId := 100) (pid : PlayerId := 1)
    (hp : Nat := 80) (blk : Nat := 0) (powers : List PowerInstance := []) : Creature :=
  { id := id
  , modelId := ModelId.mkCharacter "IRONCLAD"
  , side := .player
  , playerId := some pid
  , currentHp := hp
  , maxHp := 80
  , block := blk
  , powers := powers }

private def mkEnemyCreature (id : CreatureId := 200) (hp : Nat := 50) (blk : Nat := 0)
    (powers : List PowerInstance := []) : Creature :=
  { id := id
  , modelId := ModelId.mkMonster "JAW_WORM"
  , side := .enemy
  , currentHp := hp
  , maxHp := hp
  , block := blk
  , powers := powers }

private def mkPow (instId : PowerInstanceId) (ownerId : CreatureId) (entry : String) (amt : Int)
    (ptype : PowerType := .buff) (stype : PowerStackType := .counter)
    (itype : PowerInstanceType := .none) (applier : Option CreatureId := none)
    (allowNeg : Bool := false) : PowerInstance :=
  { instanceId := instId
  , modelId := ModelId.mkPower entry
  , ownerId := ownerId
  , applierId := applier
  , powerType := ptype
  , stackType := stype
  , instanceType := itype
  , allowNegative := allowNeg
  , amount := amt }

private def mkStrike (instId : CardInstanceId := 1) : CardInstance :=
  { instanceId := instId
  , modelId := ModelId.mkCard "STRIKE_IRONCLAD"
  , ownerId := 1
  , cardType := .attack
  , rarity := .basic
  , targetType := .anyEnemy
  , tags := [.strike]
  , energyCost := CardEnergyCost.mkCanonical 1
  , baseDamage := Dec.ofInt 6 }

def allVanillaTests : List (String × Bool) :=
  -- 1. Strike (6) + Strength (3) + Vulnerable (1.5) = 13.5 -> truncate 13
  let cs1 : CombatState :=
    { allies := [mkPlayerCreature 100 1 80 0 [mkPow 10 100 "STRENGTH_POWER" 3]]
    , enemies := [mkEnemyCreature 200 50 0 [mkPow 11 200 "VULNERABLE_POWER" 2 .debuff]]
    , players := [mkTestPlayer 1 100] }
  let d1 := (modifyDamage cs1 (builtinBehaviorRegistry cs1) (cs1.findCreature 200) (cs1.findCreature 100) (Dec.ofInt 6) DamageProps.card none).1
  let t1 := ("01_strike_strength_vulnerable", d1.truncate == 13 && Dec.format d1 == "13.5")

  -- 2. Paper Phrog boosts Vulnerable from 1.5x to 1.75x: (6+3)*1.75 = 15.75 -> 15
  let cs2 : CombatState :=
    { allies := [mkPlayerCreature 100 1 80 0 [mkPow 10 100 "STRENGTH_POWER" 3]]
    , enemies := [mkEnemyCreature 200 50 0 [mkPow 11 200 "VULNERABLE_POWER" 2 .debuff]]
    , players := [mkTestPlayer 1 100 3 0 [{ modelId := ModelId.mkRelic "PAPER_PHROG" }]] }
  let d2 := (modifyDamage cs2 (builtinBehaviorRegistry cs2) (cs2.findCreature 200) (cs2.findCreature 100) (Dec.ofInt 6) DamageProps.card none).1
  let t2 := ("02_paper_phrog_vulnerable", d2.truncate == 15 && Dec.format d2 == "15.75")

  -- 3. Weak (0.75) * Vulnerable (1.5) = 1.125: 10 * 0.75 * 1.5 = 11.25 -> 11
  let cs3 : CombatState :=
    { allies := [mkPlayerCreature 100 1 80 0 [mkPow 10 100 "WEAK_POWER" 2 .debuff]]
    , enemies := [mkEnemyCreature 200 50 0 [mkPow 11 200 "VULNERABLE_POWER" 2 .debuff]]
    , players := [mkTestPlayer 1 100] }
  let d3 := (modifyDamage cs3 (builtinBehaviorRegistry cs3) (cs3.findCreature 200) (cs3.findCreature 100) (Dec.ofInt 10) DamageProps.card none).1
  let t3 := ("03_weak_and_vulnerable_order", d3.truncate == 11 && Dec.format d3 == "11.25")

  -- 4. Unpowered damage ignores Strength and Vulnerable
  let d4 := (modifyDamage cs1 (builtinBehaviorRegistry cs1) (cs1.findCreature 200) (cs1.findCreature 100) (Dec.ofInt 6) DamageProps.nonCardUnpowered none).1
  let t4 := ("04_unpowered_bypasses_str_vuln", decide (Dec.eqVal d4 (Dec.ofInt 6)))

  -- 5. Unblockable damage bypasses Block completely
  let cs5 : CombatState :=
    { allies := [mkPlayerCreature 100 1 80 0]
    , enemies := [mkEnemyCreature 200 30 25]
    , players := [mkTestPlayer 1 100] }
  let (cs5', res5) := damageSingleTarget cs5 (builtinBehaviorRegistry cs5) 200 (Dec.ofInt 10) DamageProps.nonCardHpLoss (some 100) none
  let t5 := ("05_unblockable_bypasses_block",
    (cs5'.findCreature 200).map (fun c => c.currentHp == 20 && c.block == 25) == some true &&
    res5.head?.map (·.blockedDamage) == some 0)

  -- 6. Intangible caps HP loss at 1 after block is checked
  let cs6 : CombatState :=
    { allies := [mkPlayerCreature 100 1 80 0 [mkPow 10 100 "INTANGIBLE_POWER" 1]]
    , enemies := [mkEnemyCreature 200 50 0]
    , players := [mkTestPlayer 1 100] }
  let (cs6', res6) := damageSingleTarget cs6 (builtinBehaviorRegistry cs6) 100 (Dec.ofInt 25) DamageProps.monsterMove (some 200) none
  let t6 := ("06_intangible_caps_loss_to_1",
    (cs6'.findCreature 100).map (·.currentHp) == some 79 &&
    res6.head?.map (·.unblockedDamage) == some 1)

  -- 7. Osty DieForYou redirects powered unblocked damage & spills overkill back to owner
  let cs7Base : CombatState :=
    { allies := [mkPlayerCreature 100 1 80 5]
    , enemies := [mkEnemyCreature 200 50 0]
    , players := [mkTestPlayer 1 100] }
  let (cs7Summ, _) := summonOsty cs7Base (builtinBehaviorRegistry cs7Base) 1 (Dec.ofInt 10)
  let reg7 : BehaviorRegistry := fun mid =>
    if mid == dieForYouPowerModelId then dieForYouBehavior cs7Summ else builtinBehaviorRegistry cs7Summ mid
  let (cs7After, _) := damageSingleTarget cs7Summ reg7 100 (Dec.ofInt 20) DamageProps.monsterMove (some 200) none
  -- 20 dmg - 5 block = 15 unblocked -> Osty takes 10 (dies, overkill 5) -> Necrobinder takes 5 -> HP = 75
  let t7 := ("07_osty_die_for_you_and_overkill_spill",
    (findOsty cs7After 1).map (·.currentHp) == some 0 &&
    (cs7After.findCreature 100).map (fun c => c.currentHp == 75 && c.block == 0) == some true)

  -- 8. Dexterity (3) + Frail (0.75) on base block 8: (8 + 3) * 0.75 = 8.25 -> gainBlock truncates to 8
  let cs8 : CombatState :=
    { allies := [mkPlayerCreature 100 1 80 0 [mkPow 10 100 "DEXTERITY_POWER" 3, mkPow 11 100 "FRAIL_POWER" 2 .debuff]]
    , enemies := [mkEnemyCreature 200 50 0]
    , players := [mkTestPlayer 1 100] }
  let (cs8', blk8) := gainBlock cs8 (builtinBehaviorRegistry cs8) 100 (Dec.ofInt 8) BlockProps.card
  let t8 := ("08_dexterity_and_frail_block",
    (cs8'.findCreature 100).map (·.block) == some 8 && Dec.format blk8 == "8.25")

  -- 9. Barricade preserves block at turn start (`clearTurnStartBlock`)
  let cs9 : CombatState :=
    { allies := [mkPlayerCreature 100 1 80 18 [mkPow 10 100 "BARRICADE_POWER" 1 .buff .single]]
    , players := [mkTestPlayer 1 100] }
  let cs9Barricade := clearTurnStartBlock { cs9 with players := cs9.players.map fun p =>
      { p with combatState := p.combatState.map fun st => { st with turnNumber := 2 } } }
    (builtinBehaviorRegistry cs9) .player
  let t9 := ("09_barricade_retains_block",
    (cs9Barricade.findCreature 100).map (·.block) == some 18)

  -- 10. Turn 1 automatically skips turn-start block clear even without Barricade
  let cs10 : CombatState := { allies := [mkPlayerCreature 100 1 80 12], players := [mkTestPlayer 1 100] }
  let cs10Cleared := clearTurnStartBlock cs10 (builtinBehaviorRegistry cs10) .player
  let t10 := ("10_turn1_skips_block_clear",
    (cs10Cleared.findCreature 100).map (·.block) == some 12)

  -- 11. Artifact blocks visible debuff & decrements by 1; ignores buffs
  let cs11 : CombatState :=
    { allies := [mkPlayerCreature 100 1 80 0 [mkPow 10 100 "ARTIFACT_POWER" 1]]
    , players := [mkTestPlayer 1 100] }
  let (cs11Debuff, debRes) := applyPower cs11 (builtinBehaviorRegistry cs11)
    { instanceId := 0, modelId := ModelId.mkPower "WEAK_POWER", ownerId := 100, powerType := .debuff, stackType := .counter } 100 (Dec.ofInt 2)
  let t11 := ("11_artifact_negates_debuff_and_consumes",
    debRes.isNone &&
    (cs11Debuff.findCreature 100).map (fun c => !c.hasPower (ModelId.mkPower "ARTIFACT_POWER") && !c.hasPower (ModelId.mkPower "WEAK_POWER")) == some true)

  -- 12. Power clamping to [-999999999, 999999999]
  let t12 := ("12_power_amount_clamp",
    PowerInstance.clampAmount 2000000000 == 999999999 &&
    PowerInstance.clampAmount (-2000000000) == -999999999)

  -- 13. InstancedPerApplier separates Impaled from two appliers
  let cs13Base : CombatState :=
    { allies := [mkPlayerCreature 100 1 80 0, mkPlayerCreature 101 2 80 0]
    , enemies := [mkEnemyCreature 200 50 0]
    , players := [mkTestPlayer 1 100, mkTestPlayer 2 101] }
  let tmplImp : PowerInstance :=
    { instanceId := 0, modelId := impaledPowerModelId, ownerId := 200, powerType := .none, stackType := .counter, instanceType := .instancedPerApplier }
  let (cs13a, _) := applyPower cs13Base (fun _ => HookBehavior.neutral) tmplImp 200 Dec.one (some 100)
  let (cs13b, _) := applyPower cs13a (fun _ => HookBehavior.neutral) tmplImp 200 Dec.one (some 101)
  let t13 := ("13_instanced_per_applier_separation",
    ((cs13b.findCreature 200).map (fun c => (c.getPowerInstances impaledPowerModelId).length)) == some 2)

  -- 14. Local cost modifiers (relative reduction, canonical unaffected)
  let e14Clean : CardEnergyCost :=
    { canonical := 2, baseCost := 2
    , localModifiers := [{ amount := -1, costType := .relative, expiration := LocalCostModifierExpiration.onlyEndOfTurn }] }
  let t14 := ("14_local_cost_modifier_relative",
    e14Clean.getWithModifiers false == 1 && e14Clean.getWithModifiers true == 2)

  -- 15. X-cost card spends all energy & records capturedXValue
  let xCard : CardInstance :=
    { instanceId := 50, modelId := ModelId.mkCard "WHIRLWIND", ownerId := 1, cardType := .attack
    , rarity := .uncommon, targetType := .allEnemies, energyCost := CardEnergyCost.mkCanonical 0 true }
  let pcs15 : PlayerCombatState := { energy := 4, baseMaxEnergy := 3, piles := { hand := [xCard] } }
  let cs15 : CombatState :=
    { allies := [mkPlayerCreature 100 1 80 0]
    , enemies := [mkEnemyCreature 200 50 0]
    , players := [{ (mkTestPlayer 1 100 4) with combatState := some pcs15 }] }
  let (cs15', ok15) := playCard cs15 (builtinBehaviorRegistry cs15) 1 50 none
  let t15 := ("15_x_cost_spends_all_energy",
    ok15 && (cs15'.findPlayer 1 |>.bind (·.combatState)).map (·.energy == 0) == some true)

  -- 16. Draw reshuffles discard into draw preserving total cards & respects hand cap 10
  let p16 := mkTestPlayer 1 100 3
  let cards16 := (List.range 12).map fun i => mkStrike (i + 1)
  let pcs16 : PlayerCombatState :=
    { energy := 3, baseMaxEnergy := 3
    , piles := { draw := cards16.take 2, discard := cards16.drop 2 } }
  let cs16 : CombatState := { players := [{ p16 with combatState := some pcs16 }], rng := Rng.ofSeed 42 }
  let (cs16', drawn16) := drawCards cs16 (builtinBehaviorRegistry cs16) 1 11 true
  let pcs16' := (cs16'.findPlayer 1 |>.bind (·.combatState))
  let t16 := ("16_draw_reshuffle_and_hand_limit_10",
    drawn16.length == 10 &&
    pcs16'.map (fun st => st.piles.hand.length == 10 && st.piles.totalCount == 12) == some true)

  -- 17. Turn End Phase 1 exhausts Ethereal & Phase 2 keeps Retain while flushing rest
  let ethCard : CardInstance := { (mkStrike 1) with keywords := [.ethereal] }
  let retCard : CardInstance := { (mkStrike 2) with keywords := [.retain] }
  let regCard : CardInstance := mkStrike 3
  let pcs17 : PlayerCombatState := { energy := 3, baseMaxEnergy := 3, piles := { hand := [ethCard, retCard, regCard] } }
  let cs17 : CombatState :=
    { allies := [mkPlayerCreature 100 1 80 0]
    , enemies := [mkEnemyCreature 200 50 0]
    , players := [{ (mkTestPlayer 1 100 3) with combatState := some pcs17 }] }
  let cs17a := endPlayerTurnPhaseOne cs17 (builtinBehaviorRegistry cs17)
  let cs17b := endPlayerTurnPhaseTwo cs17a (builtinBehaviorRegistry cs17a)
  let t17 := ("17_ethereal_exhaust_and_retain_kept",
    (cs17b.findPlayer 1 |>.bind (·.combatState)).map (fun st =>
      st.piles.exhaust.length == 1 && st.piles.hand.length == 1 && st.piles.discard.length == 1) == some true)

  -- 18. PendingLoss overrides dead enemies to yield Defeat
  let cs18 : CombatState := { enemies := [mkEnemyCreature 200 0 0], pendingLoss := some ⟨1⟩ }
  let t18 := ("18_pending_loss_beats_victory",
    (checkWinCondition cs18 (fun _ => HookBehavior.neutral)).2 == .defeat)

  -- 19. ShouldStopCombatFromEnding blocks Victory when all primary enemies are dead
  let stopReg : BehaviorRegistry := fun _ => { HookBehavior.neutral with shouldStopCombatFromEnding := fun _ => true }
  let cs19 : CombatState := { enemies := [mkEnemyCreature 200 0 0], runModels := [⟨"RUN", "PHASE_BOSS"⟩] }
  let t19 := ("19_should_stop_combat_from_ending",
    (checkWinCondition cs19 stopReg).2 == .ongoing)

  -- 20. MonsterStateMachine traverses RandomBranch -> ConditionalBranch -> MoveState deterministically
  let sm20 : MonsterStateMachine :=
    { initialStateId := "RAND"
    , currentStateId := "RAND"
    , nodes := fun sid =>
        if sid == "RAND" then some { id := "RAND", kind := .randomBranch [("COND", 1), ("M2", 1)] }
        else if sid == "COND" then some { id := "COND", kind := .conditionalBranch [(fun _ c => (c.currentHp < 30, "M1"))] "M2" }
        else if sid == "M1" then some { id := "M1", kind := .move "" true false }
        else if sid == "M2" then some { id := "M2", kind := .move "M1" true false }
        else none }
  let owner20 := mkEnemyCreature 200 20 0
  let r20a := sm20.rollMoveFuel 8 cs18 owner20 (Rng.ofSeed 99)
  let r20b := sm20.rollMoveFuel 8 cs18 owner20 (Rng.ofSeed 99)
  let t20 := ("20_monster_ai_deterministic",
    r20a.isSome && r20a.map (·.1) == r20b.map (·.1) && r20a.map (·.2.1.stateLog) == r20b.map (·.2.1.stateLog))

  -- 21. Defect Orbs: Focus boosts Lightning/Frost/Glass/Dark while Plasma is immune; Glass decays passive by 1
  let glassOrb := OrbInstance.mkDefault 1 .glass
  let plasmaOrb := OrbInstance.mkDefault 2 .plasma
  let pcs21 : PlayerCombatState := { energy := 3, baseMaxEnergy := 3, orbQueue := { capacity := 3, orbs := [glassOrb, plasmaOrb] } }
  let cs21 : CombatState :=
    { allies := [mkPlayerCreature 100 1 80 0 [mkPow 10 100 "FOCUS_POWER" 2]]
    , enemies := [mkEnemyCreature 200 50 0]
    , players := [{ (mkTestPlayer 1 100 3) with combatState := some pcs21 }] }
  let cs21Start := triggerTurnStartOrbs cs21 (builtinBehaviorRegistry cs21) 1 -- Plasma gives +1 energy
  let cs21End := triggerTurnEndOrbs cs21Start (builtinBehaviorRegistry cs21Start) 1 -- Glass deals 4+2=6 dmg & decays basePassive to 3
  let t21 := ("21_defect_orbs_plasma_and_glass_focus",
    effectivePassiveVal 2 plasmaOrb == Dec.ofInt 1 &&
    effectiveEvokeVal 2 glassOrb == Dec.ofInt 12 &&
    (cs21End.findCreature 200).map (·.currentHp) == some 44 &&
    (cs21End.findPlayer 1 |>.bind (·.combatState)).map (·.energy) == some 4)

  -- 22. Necrobinder Doom executes iff currentHp <= DoomPower amount
  let doomedEnemy := mkEnemyCreature 200 15 0 [mkPow 10 200 "DOOM_POWER" 15 .debuff]
  let safeEnemy := mkEnemyCreature 201 16 0 [mkPow 11 201 "DOOM_POWER" 15 .debuff]
  let cs22 : CombatState := { allies := [mkPlayerCreature 100 1], enemies := [doomedEnemy, safeEnemy] }
  let cs22' := triggerSideDoomKill cs22 (fun _ => HookBehavior.neutral) .enemy
  let t22 := ("22_necrobinder_doom_kill",
    (cs22'.findCreature 200).map (·.isDead) == some true &&
    (cs22'.findCreature 201).map (·.isAlive) == some true)

  -- 23. Regent Forge generates SovereignBlade on first forge and scales damage across piles
  let cs23Base : CombatState := { allies := [mkPlayerCreature 100 1], players := [mkTestPlayer 1 100 1 4] }
  let cs23a := forgeSovereignBlade cs23Base 1 (Dec.ofInt 5) -- 10 + 5 = 15
  let cs23b := forgeSovereignBlade cs23a 1 (Dec.ofInt 7)    -- 15 + 7 = 22
  let t23 := ("23_regent_forge_sovereign_blade",
    (cs23b.findPlayer 1 |>.bind (·.combatState)).map (fun st =>
      let blades := getSovereignBlades st true
      blades.length == 1 && blades.head?.map (fun b => decide (Dec.eqVal b.baseDamage (Dec.ofInt 22))) == some true) == some true)

  -- 24. Regent Excess Energy with Stars: 1 energy + 2 stars can pay a 2-cost card!
  let pcs24 : PlayerCombatState := { energy := 1, baseMaxEnergy := 3, stars := 2 }
  let (eReq24, sReq24, r24) := pcs24.checkResourcesFor 2 0 true
  let t24 := ("24_regent_excess_energy_with_stars",
    r24.isPlayable && eReq24 == 1 && sReq24 == 2)

  -- 25. Fool Arrow: shoot -> ImpaledPower -> dislodge returns arrow; destroyAfterImpaled destroys instead
  let cs25Base : CombatState :=
    { allies := [mkPlayerCreature 100 1], enemies := [mkEnemyCreature 200 50 0], players := [mkTestPlayer 1 100] }
  let cs25Slot := gainArrowSlot cs25Base 1 false
  let (cs25Shot, idxOpt) := shootArrowAtTarget cs25Slot (builtinBehaviorRegistry cs25Slot) 1 200
  let cs25Dis := match idxOpt with | some idx => dislodgeArrow cs25Shot 1 200 idx | none => cs25Shot
  let t25 := ("25_fool_arrow_shoot_impale_dislodge",
    availableArrowCount cs25Shot 1 == 0 &&
    availableArrowCount cs25Dis 1 == 1 &&
    (cs25Shot.findCreature 200).map (·.hasPower impaledPowerModelId) == some true)

  -- 26. Fool Melody distinct tag counter (`Wah`, `Cho`, `Ki`) <= 3
  let pld : CardPlay := { cardId := 10, playerId := 1 }
  let cs26 : CombatState :=
    { roundNumber := 1
    , players := [mkTestPlayer 1 100]
    , history :=
        [ .cardPlayStarted 1 .player pld [.wah, .cho]
        , .cardPlayFinished 1 .player pld [.wah, .cho]
        , .cardPlayFinished 1 .player { pld with cardId := 11 } [.wah] ] }
  let t26 := ("26_fool_melody_distinct_tags_and_identity",
    melodiesThisTurn cs26 1 == 2 &&
    melodyCardsPlayedThisTurn cs26 1 == 2 &&
    isFirstMelodyPlayThisTurn cs26 pld .wah &&
    !(isFirstMelodyPlayThisTurn cs26 { pld with cardId := 11 } .wah))

  -- 27. Dread lifecycle adds Ascender's Bane in Act > 0 and clears Dominion at Boss room
  let cfg27 : DreadActConfig := { actIndex := 1, bossEncounterId := ⟨"ENCOUNTER", "VANTOM_BOSS"⟩, dominionId := ModelId.mkDominion "VANTOM_DOMINION" }
  let rs27 : RunState := { players := [mkTestPlayer 1 100] }
  let (rs27Act, _) := dreadAfterActEntered rs27 cfg27 500
  let (rs27Boss, cs27Boss) := dreadBeforeRoomEntered rs27Act { dominion := rs27Act.dominion } .boss cfg27.bossEncounterId cfg27
  let t27 := ("27_dread_ascenders_bane_and_boss_clear",
    rs27Act.players.head?.map (·.deck.length) == some 1 &&
    rs27Boss.dominion.isNone && cs27Boss.dominion.isNone)

  -- 28. CardRarityOdds: Boss yields Rare & Rare resets offset to -0.05; non-Rare grows by +0.01
  let odds28 : CardRarityOddsDec := { offset := Dec.ofScaled 10 2 }
  let (rBoss, oddsBoss) := odds28.rollFromSample .bossEncounter (Dec.ofScaled 5 1)
  let (rCom, oddsCom) := odds28.rollFromSample .regularEncounter (Dec.ofScaled 95 2)
  let t28 := ("28_card_rarity_odds_pity_and_boss",
    rBoss == .rare && oddsBoss.offset == CardRarityOddsDec.baseOffset &&
    rCom == .common && decide (Dec.eqVal oddsCom.offset (Dec.ofScaled 11 2)))

  -- 29. RelicGrabBag fallback chain (`Shop -> Common -> Uncommon -> Rare -> fallback`)
  let bag29 : RelicGrabBag := { common := [ModelId.mkRelic "VAJRA"], fallback := [ModelId.mkRelic "AKABEKO"] }
  let (bag29', r1) := bag29.pullFromFront .shop -- Shop empty -> pulls Common VAJRA
  let (bag29'', r2) := bag29'.pullFromFront .common -- Now queues empty -> pulls Fallback AKABEKO
  let t29 := ("29_relic_grab_bag_fallback",
    r1 == some (ModelId.mkRelic "VAJRA") && r2 == some (ModelId.mkRelic "AKABEKO") && bag29''.totalCount == 0)

  -- 30. ActMap path traversal & Catalog sanity lookup (`STRIKE_IRONCLAD`, 717/316/304)
  let map30 : ActMap :=
    { mapLength := 2
    , startPoint := ⟨3, 0⟩
    , bossPoint := ⟨3, 2⟩
    , points :=
        [ { coord := ⟨3, 0⟩, pointType := .unassigned, children := [⟨3, 1⟩] }
        , { coord := ⟨3, 1⟩, pointType := .monster, children := [⟨3, 2⟩] }
        , { coord := ⟨3, 2⟩, pointType := .boss, children := [] } ] }
  let t30 := ("30_act_map_and_catalog_lookup",
    map30.hasEdge ⟨3, 0⟩ ⟨3, 1⟩ && map30.hasEdge ⟨3, 1⟩ ⟨3, 2⟩ &&
    (lookupCard "STRIKE_IRONCLAD").map (·.baseCost) == some 1 &&
    (lookupRelic "PAPER_PHROG").isSome &&
    (lookupPower "VULNERABLE_POWER").isSome)

  [ t1, t2, t3, t4, t5, t6, t7, t8, t9, t10
  , t11, t12, t13, t14, t15, t16, t17, t18, t19, t20
  , t21, t22, t23, t24, t25, t26, t27, t28, t29, t30 ]

end Sts2Model.Examples
