/-
  Executable Showcase for the generic headless multiplayer timeline & simulator core:
  concurrent ActionQueueSet scheduling, early-resume buffering, keyframe seek equivalence
  with 64-bit FNV-1a checksums, viewer-perspective switching, potions + monster AI rounds,
  and generic OpaqueStateDelta fallback.
-/
import Sts2Model.Proofs.ReplayTimeline
import Sts2Model.Sim.VanillaEffects

namespace Sts2Model.Examples

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Multiplayer
open Sts2Model.Sim
open Sts2Model.Replay
open Sts2Model.Proofs

private def sampleBashCard : CardInstance :=
  { instanceId := 1001, modelId := ModelId.mkCard "BASH", ownerId := 1
  , cardType := .attack, rarity := .basic, targetType := .anyEnemy
  , energyCost := CardEnergyCost.mkCanonical 2 }

private def sampleTwinStrikeCard : CardInstance :=
  { instanceId := 2001, modelId := ModelId.mkCard "TWIN_STRIKE", ownerId := 2
  , cardType := .attack, rarity := .common, targetType := .anyEnemy
  , energyCost := CardEnergyCost.mkCanonical 1 }

private def sampleStrikePlusCard : CardInstance :=
  { instanceId := 2002, modelId := ModelId.mkCard "STRIKE_IRONCLAD", ownerId := 2
  , cardType := .attack, rarity := .basic, targetType := .anyEnemy
  , energyCost := CardEnergyCost.mkCanonical 1, upgradeLevel := 1 }

private def sampleCoopGuardian : Creature :=
  { id := 200, modelId := ModelId.mkMonster "COOP_GUARDIAN", side := .enemy
  , currentHp := 34, maxHp := 34
  , monster := some { modelId := ModelId.mkMonster "COOP_GUARDIAN", currentMoveId := "SLAM" } }

private def sampleCoopInit : TimelineState :=
  let cP1 : Creature :=
    { id := 101, modelId := ModelId.mkCharacter "IRONCLAD", side := .player, playerId := some 1
    , currentHp := 80, maxHp := 80 }
  let cP2 : Creature :=
    { id := 102, modelId := ModelId.mkCharacter "SILENT", side := .player, playerId := some 2
    , currentHp := 70, maxHp := 70 }
  let p1 : Player :=
    { playerId := 1, creatureId := 101, characterId := ModelId.mkCharacter "IRONCLAD"
    , combatState := some { energy := 3, piles := { hand := [sampleBashCard] } } }
  let p2 : Player :=
    { playerId := 2, creatureId := 102, characterId := ModelId.mkCharacter "SILENT"
    , combatState := some { energy := 3, piles := { hand := [sampleTwinStrikeCard, sampleStrikePlusCard] } } }
  let cs : CombatState :=
    { combatId := 1, roundNumber := 1, currentSide := .player, isInProgress := true
    , allies := [cP1, cP2], enemies := [sampleCoopGuardian], players := [p1, p2]
    , rng := Rng.ofSeed 42 }
  { combat := some cs
  , queueSet := (ActionQueueSet.init [1, 2]).combatStarted
  , choiceSync := PlayerChoiceSynchronizer.init [1, 2] }

private def mkSamplePlayEv (seqIdx : Nat) (pid : PlayerId) (cid : CardInstanceId) (tid : CreatureId) : TimelineEvent :=
  { seqIdx := seqIdx, actIndex := 0, floor := 1, roundNumber := 1, actorPlayerId := pid
  , kind := .combat { eventType := .gameAction, playerId := some pid, payload := some (.playCard cid (some tid)) } }

private def potionAndRoundEvents : List TimelineEvent :=
  [ mkSamplePlayEv 0 2 2001 200
  , mkSamplePlayEv 1 2 2002 200
  , mkSamplePlayEv 2 1 1001 200
  , { seqIdx := 3, actIndex := 0, floor := 1, roundNumber := 1, actorPlayerId := 1
    , kind := .endRoundAndRunEnemies }
  , { seqIdx := 4, actIndex := 0, floor := 1, roundNumber := 2, actorPlayerId := 1
    , kind := .opaqueStep { label := "COOP_BONUS", blockDeltas := [(101, 5)], energyDeltas := [(1, 1)] } } ]

def tl_01_concurrent_queues_player_choice_pause_resume : Bool :=
  let qs0 := (ActionQueueSet.init [1, 2]).combatStarted
  let (qs1, id1, acc1) := qs0.enqueue 1 .combatPlayPhaseOnly true true (.playCard 1001 (some 200))
  let (qs2, id2, acc2) := qs1.enqueue 2 .combatPlayPhaseOnly true true (.playCard 2001 (some 200))
  let (qs3, r1) := qs2.getReadyAction
  let (qs4, pauseOk) := qs3.pauseActionForPlayerChoice id1 { cancelPlayCardActions := true }
  -- Extra PlayCard queued by P1 while paused for choice must be canceled
  let (qs5, _, accCancelled) := qs4.enqueue 1 .combatPlayPhaseOnly true true (.playCard 1002 (some 200))
  -- Meanwhile P2's head action (`id2`) must be immediately ready and unblocked!
  let (qs6, r2) := qs5.getReadyAction
  let qs7 := qs6.popAction id2
  let (qs8, newId) := qs7.resumeAction id1
  let (_, r3) := qs8.getReadyAction
  acc1 && acc2 && !accCancelled && pauseOk &&
  qs5.canceledCount == 1 &&
  (r1.map (·.actionId) == some id1) &&
  (r2.map (·.actionId) == some id2) &&
  (r3.map (·.actionId) == some newId) &&
  (r3.map (·.state) == some .readyToResumeExecuting)

def tl_02_early_resume_buffered_before_pause : Bool :=
  let act : QueuedAction :=
    { actionId := 5, ownerId := 1, actionType := .combatPlayPhaseOnly
    , isPlayerDriven := true, isPlayCard := true, state := .executing
    , payload := .playCard 1001 none }
  let qs : ActionQueueSet :=
    { queues := [{ ownerId := 1, actions := [act], isCancellingCombatActions := false }]
    , nextActionId := 10, isInCombat := true }
  let (qs1, newId) := qs.resumeAction 5
  let (qs2, pausedOk) := qs1.pauseActionForPlayerChoice 5 {}
  let (_, readyOpt) := qs2.getReadyAction
  newId == 10 && pausedOk && qs2.waitingForResumption.isEmpty &&
  (readyOpt.map (·.actionId) == some 10) &&
  (readyOpt.map (·.state) == some .readyToResumeExecuting)

def tl_03_keyframe_seek_matches_full_replay_and_checksum : Bool :=
  let archive := buildArchive vanillaEffectEnv sampleCoopInit potionAndRoundEvents 2 1
  let indices := List.range (potionAndRoundEvents.length + 1)
  indices.all fun k =>
    let sSeek := seek vanillaEffectEnv archive k
    let sFull := replayEvents vanillaEffectEnv sampleCoopInit (potionAndRoundEvents.take k)
    sSeek == sFull && computeStateChecksum sSeek == computeStateChecksum sFull

def tl_04_viewer_switch_invariance : Bool :=
  let a1 := buildArchive vanillaEffectEnv sampleCoopInit potionAndRoundEvents 2 1
  let a2 := switchViewer a1 2
  let indices := List.range (potionAndRoundEvents.length + 1)
  indices.all fun k =>
    let s1 := seek vanillaEffectEnv a1 k
    let s2 := seek vanillaEffectEnv a2 k
    s1 == s2 && computeStateChecksum s1 == computeStateChecksum s2

def tl_05_potion_and_monster_ai_turn_cycle : Bool :=
  let initPot :=
    match sampleCoopInit.combat with
    | none => sampleCoopInit
    | some cs =>
        let csP := cs.updatePlayer 1 fun p =>
          { p with potions := [some { modelId := ModelId.mkPotion "FIRE_POTION" }] }
        { sampleCoopInit with combat := some csP }
  let evs : List TimelineEvent :=
    [ { seqIdx := 0, roundNumber := 1, actorPlayerId := 1
      , kind := .combat { eventType := .gameAction, playerId := some 1
                        , payload := some (.usePotion 0 (some 200)) } }
    , { seqIdx := 1, roundNumber := 1, actorPlayerId := 1, kind := .endRoundAndRunEnemies } ]
  let stFinal := replayEvents vanillaEffectEnv initPot evs
  match stFinal.combat with
  | none => false
  | some cs =>
      let eHp := (cs.findCreature 200).map (·.currentHp) |>.getD 999
      let p1Hp := (cs.findCreature 101).map (·.currentHp) |>.getD 999
      let p2Hp := (cs.findCreature 102).map (·.currentHp) |>.getD 999
      let hasPotHist := stFinal.combatHistory.any fun te =>
        match te.entry with | .potionUsed .. => true | _ => false
      let hasMonsterMove := stFinal.combatHistory.any fun te =>
        match te.entry with | .monsterPerformedMove _ _ 200 _ "SLAM" _ => true | _ => false
      -- Fire Potion dealt 20 unpowered dmg (34 -> 14), Guardian SLAM dealt 7 to P1 (80->73) & P2 (70->63), advanced to round 2
      eHp == 14 && p1Hp == 73 && p2Hp == 63 && cs.roundNumber == 2 &&
      hasPotHist && hasMonsterMove &&
      ((cs.findPlayer 1).bind (·.combatState)).map (·.energy) == some 3

def tl_06_opaque_state_delta_fallback : Bool :=
  let ev : TimelineEvent :=
    { seqIdx := 0, roundNumber := 1, actorPlayerId := 1
    , kind := .opaqueStep
        { label := "RELIC_CUSTOM_TRIGGER"
        , hpDeltas := [(200, -5)]
        , blockDeltas := [(101, 4)]
        , energyDeltas := [(1, 1)]
        , starsDeltas := [(2, 3)] } }
  let st := replayEvents vanillaEffectEnv sampleCoopInit [ev]
  match st.combat with
  | none => false
  | some cs =>
      let eHp := (cs.findCreature 200).map (·.currentHp) |>.getD 0
      let p1Blk := (cs.findCreature 101).map (·.block) |>.getD 0
      let p1Eng := ((cs.findPlayer 1).bind (·.combatState)).map (·.energy) |>.getD 0
      let p2Stars := ((cs.findPlayer 2).bind (·.combatState)).map (·.stars) |>.getD 0
      eHp == 29 && p1Blk == 4 && p1Eng == 4 && p2Stars == 3

def sampleTraceArchive : TimelineArchive :=
  buildArchive vanillaEffectEnv sampleCoopInit potionAndRoundEvents 2 1

def sampleTraceBundle : WireTraceBundle :=
  encodeArchiveBundle sampleTraceArchive 2

def tl_07_fork_timeline_matches_prefix_plus_alt : Bool :=
  let altEvs : List TimelineEvent :=
    [ mkSamplePlayEv 0 1 1001 200
    , mkSamplePlayEv 1 2 2001 200
    , mkSamplePlayEv 2 2 2002 200 ]
  let forked := forkTimeline vanillaEffectEnv sampleTraceArchive 0 altEvs
  let direct := replayEvents vanillaEffectEnv sampleCoopInit altEvs
  forked == direct && computeStateChecksum forked == computeStateChecksum direct

def tl_08_trace_json_roundtrip_preserves_seek_and_checksums : Bool :=
  let rawJson := serializeTraceJson sampleTraceBundle false
  match parseTraceJson rawJson with
  | .error _ => false
  | .ok decodedBundle =>
      match decodeArchiveBundle vanillaEffectEnv decodedBundle with
      | .error _ => false
      | .ok decodedArch =>
          let audit := verifyTraceChecksums vanillaEffectEnv decodedArch decodedBundle.expectedChecksums
          let indices := List.range (potionAndRoundEvents.length + 1)
          let matchAll := indices.all fun k =>
            let s1 := seek vanillaEffectEnv sampleTraceArchive k
            let s2 := seek vanillaEffectEnv decodedArch k
            s1 == s2 && computeStateChecksum s1 == computeStateChecksum s2
          audit.allMatched && matchAll

def tl_09_trace_json_rejects_unsupported_schema_version : Bool :=
  let badBundle : WireTraceBundle := { sampleTraceBundle with schemaVersion := 99 }
  match decodeArchiveBundle vanillaEffectEnv badBundle with
  | .error _ => true
  | .ok _    => false

def tl_10_verify_trace_checksums_detects_tampering : Bool :=
  let tampered :=
    match sampleTraceBundle.expectedChecksums with
    | [] => []
    | c :: rest => { c with checksum := "12345" } :: rest
  let audit := verifyTraceChecksums vanillaEffectEnv sampleTraceArchive tampered
  !audit.allMatched && audit.mismatches.length == 1

def tl_11_lifecycle_debuff_skip_tick_and_poison_doom : Bool :=
  let cP1 : Creature :=
    { id := 101, modelId := ModelId.mkCharacter "IRONCLAD", side := .player, playerId := some 1
    , currentHp := 80, maxHp := 80
    , powers := [{ mkPoisonPower 4 101 with instanceId := 10 }] }
  let cE1 : Creature :=
    { id := 200, modelId := ModelId.mkMonster "LC_VULN", side := .enemy
    , currentHp := 10, maxHp := 40
    , monster := some { modelId := ModelId.mkMonster "LC_VULN", currentMoveId := "HEX" } }
  let p1 : Player :=
    { playerId := 1, creatureId := 101, characterId := ModelId.mkCharacter "IRONCLAD"
    , combatState := some { energy := 3, baseMaxEnergy := 3 } }
  let lcBp : MonsterBlueprint :=
    { modelId := ModelId.mkMonster "LC_VULN"
    , stateMachine :=
        { initialStateId := "HEX", currentStateId := "HEX"
        , nodes := fun sid =>
            if sid == "HEX" then some { id := "HEX", kind := .move "HEX" true false } else none }
    , moveEffects := fun _ =>
        [.applyPower .allAllies (mkVulnerablePower 1) (Dec.ofInt 2)] }
  let lcEnv : EffectEnv :=
    { tier1EffectEnv with
      monsterBlueprint := fun mid =>
        if mid.entry == "LC_VULN" then some lcBp else vanillaMonsterBlueprint mid }
  let cs0 : CombatState :=
    { combatId := 1, roundNumber := 1, currentSide := .player, isInProgress := true
    , allies := [cP1], enemies := [cE1], players := [p1], nextInstanceId := 100 }
  -- Round 1 end: enemy applies Vulnerable 2 during enemy turn (skipNextDurationTick = true -> stays 2 at R1 end)
  -- Poison ticks at R2 player turn start: P1 takes 4 unblockable dmg (80 -> 76) & Poison decrements 4 -> 3.
  let (cs1, _, _, _, _) := execEnemyTurnHeadless lcEnv cs0
  let p1AfterR1 := cs1.findCreature 101
  let vulnR1 := p1AfterR1.bind (·.getPower (ModelId.mkPower "VULNERABLE_POWER"))
  let poisR1 := p1AfterR1.bind (·.getPowerAmount (ModelId.mkPower "POISON_POWER") |> some)
  let okR1 :=
    (p1AfterR1.map (·.currentHp) == some 76) &&
    (vulnR1.map (·.amount) == some 2) &&
    (vulnR1.map (·.skipNextDurationTick) == some false) &&
    (poisR1 == some 3)
  -- Doom check: Doom >= enemy HP executes kill during BeforeSideTurnEnd(.enemy)
  let csDoom : CombatState :=
    cs0.updateCreature 200 fun c =>
      { c with powers := [{ mkDoomPower 12 200 with instanceId := 20 }] }
  let (csAfterDoom, _, _, _, _) := execEnemyTurnHeadless lcEnv csDoom
  let vulnDoom := (csAfterDoom.findCreature 101).bind (·.getPower (ModelId.mkPower "VULNERABLE_POWER"))
  let okDoom :=
    !csAfterDoom.isInProgress &&
    (csAfterDoom.findCreature 200).map (·.currentHp) == some 0 &&
    vulnDoom.map (·.amount) == some 2 &&
    vulnDoom.map (·.skipNextDurationTick) == some true
  let csEnemyPois : CombatState :=
    cs0.updateCreature 200 fun c =>
      { c with powers := [{ mkPoisonPower 12 200 with instanceId := 21 }] }
  let (csAfterPois, _, _, _, _) := execEnemyTurnHeadless lcEnv csEnemyPois
  let okEnemyPoisKill :=
    !csAfterPois.isInProgress &&
    (csAfterPois.findCreature 200).map (·.currentHp) == some 0 &&
    ((csAfterPois.findCreature 101).bind (·.getPower (ModelId.mkPower "VULNERABLE_POWER"))).isNone
  okR1 && okDoom && okEnemyPoisKill

def tl_12_lifecycle_thorns_plating_ritual_and_orbs : Bool :=
  let cP1 : Creature :=
    { id := 101, modelId := ModelId.mkCharacter "DEFECT", side := .player, playerId := some 1
    , currentHp := 80, maxHp := 80
    , powers :=
        [ { mkThornsPower 4 101 with instanceId := 11 }
        , { mkPlatingPower 3 101 with instanceId := 12 }
        , { mkFocusPower 2 101 with instanceId := 13 } ] }
  let cE1 : Creature :=
    { id := 200, modelId := ModelId.mkMonster "LC_RITUAL", side := .enemy
    , currentHp := 50, maxHp := 50
    , monster := some { modelId := ModelId.mkMonster "LC_RITUAL", currentMoveId := "BUFF" } }
  let oq : OrbQueue :=
    { capacity := 3
    , orbs :=
        [ OrbInstance.mkDefault 1 .plasma
        , OrbInstance.mkDefault 2 .lightning ] }
  let p1 : Player :=
    { playerId := 1, creatureId := 101, characterId := ModelId.mkCharacter "DEFECT"
    , baseOrbSlots := 3
    , combatState := some { energy := 3, baseMaxEnergy := 3, orbQueue := oq } }
  let bp : MonsterBlueprint :=
    { modelId := ModelId.mkMonster "LC_RITUAL"
    , stateMachine :=
        { initialStateId := "BUFF", currentStateId := "BUFF"
        , nodes := fun sid =>
            if sid == "BUFF" then some { id := "BUFF", kind := .move "SLAM" true true }
            else if sid == "SLAM" then some { id := "SLAM", kind := .move "SLAM" true false }
            else none }
    , moveEffects := fun mid =>
        if mid == "BUFF" then [.applyPower .self (mkRitualPower 1) (Dec.ofInt 2)]
        else [.dealDamage .allAllies (Dec.ofInt 6) 1 DamageProps.monsterMove] }
  let lcEnv : EffectEnv :=
    { tier1EffectEnv with
      monsterBlueprint := fun mid =>
        if mid.entry == "LC_RITUAL" then some bp else vanillaMonsterBlueprint mid }
  let cs0 : CombatState :=
    { combatId := 1, roundNumber := 1, currentSide := .player, isInProgress := true
    , allies := [cP1], enemies := [cE1], players := [p1], nextInstanceId := 100 }
  -- Turn 1: Plating +3 block (end player turn), Lightning (3+2=5 dmg -> enemy 45 HP),
  -- Enemy BUFF applies Ritual 2 (skipNextDurationTick cleared on R1 -> Strength stays 0),
  -- Turn 2 start: Turn 1 block NOT kept because TurnNumber became 2, wait turnNumber=2 clears block,
  -- Plating skips decay on player turn 1 only; at start of turn 2 Plating decays 3 -> 2, Plasma +1 energy -> 4!
  let (cs1, _, _, _, _) := execEnemyTurnHeadless lcEnv cs0
  let okR1 :=
    (cs1.findCreature 200).map (·.currentHp) == some 45 &&
    (cs1.findCreature 200).map (·.getPowerAmount (ModelId.mkPower "STRENGTH_POWER")) == some 0 &&
    (cs1.findCreature 200).map (·.getPowerAmount (ModelId.mkPower "RITUAL_POWER")) == some 2 &&
    (cs1.findCreature 101).map (·.getPowerAmount (ModelId.mkPower "PLATING_POWER")) == some 2 &&
    ((cs1.findPlayer 1).bind (·.combatState)).map (·.energy) == some 4
  -- Turn 2: Lightning deals 5 more (45->40), Enemy SLAM (6 dmg) triggers P1 Thorns (40->36),
  -- Enemy AfterSideTurnEnd fires Ritual 2 -> Strength = 2!
  let (cs2, _, _, _, _) := execEnemyTurnHeadless lcEnv cs1
  let okR2 :=
    (cs2.findCreature 200).map (·.currentHp) == some 36 &&
    (cs2.findCreature 200).map (·.getPowerAmount (ModelId.mkPower "STRENGTH_POWER")) == some 2 &&
    (cs2.findCreature 101).map (·.getPowerAmount (ModelId.mkPower "PLATING_POWER")) == some 1
  okR1 && okR2

def tl_13_tier2_card_and_potion_effects_and_upgrade : Bool :=
  let cP1 : Creature :=
    { id := 101, modelId := ModelId.mkCharacter "SILENT", side := .player, playerId := some 1
    , currentHp := 70, maxHp := 70 }
  let cE1 : Creature :=
    { id := 200, modelId := ModelId.mkMonster "BIG_DUMMY", side := .enemy
    , currentHp := 80, maxHp := 80 }
  let baseSucker : CardInstance :=
    { instanceId := 1001, modelId := ModelId.mkCard "SUCKER_PUNCH", ownerId := 1
    , cardType := .attack, rarity := .common, targetType := .anyEnemy
    , energyCost := CardEnergyCost.mkCanonical 1, upgradeLevel := 0 }
  let upgSucker : CardInstance := { baseSucker with instanceId := 1002, upgradeLevel := 1 }
  let p1 : Player :=
    { playerId := 1, creatureId := 101, characterId := ModelId.mkCharacter "SILENT"
    , potions := [some { modelId := ModelId.mkPotion "HEART_OF_IRON" }, some { modelId := ModelId.mkPotion "POTION_OF_DOOM" }]
    , combatState := some { energy := 3, baseMaxEnergy := 3, piles := { hand := [baseSucker, upgSucker] } } }
  let cs0 : CombatState :=
    { combatId := 1, allies := [cP1], enemies := [cE1], players := [p1], nextInstanceId := 500 }
  let base := execPlayCardHeadless fullVanillaEffectEnv cs0 1 1001 (some 200)
  let upg := execPlayCardHeadless fullVanillaEffectEnv cs0 1 1002 (some 200)
  let (csBase, okB) := (base.combat, base.accepted && base.pending.isNone)
  let (csUpg, okU) := (upg.combat, upg.accepted && upg.pending.isNone)
  let (csPot1, okP1, _, _, _, _) := execUsePotionHeadless fullVanillaEffectEnv csBase 1 0 none
  let (csPot2, okP2, _, _, _, _) := execUsePotionHeadless fullVanillaEffectEnv csPot1 1 1 (some 200)
  okB && okU && okP1 && okP2 &&
  (csBase.findCreature 200).map (·.currentHp) == some 72 &&
  (csBase.findCreature 200).map (·.getPowerAmount (ModelId.mkPower "WEAK_POWER")) == some 1 &&
  (csUpg.findCreature 200).map (·.currentHp) == some 70 &&
  (csUpg.findCreature 200).map (·.getPowerAmount (ModelId.mkPower "WEAK_POWER")) == some 2 &&
  (csPot2.findCreature 101).map (·.getPowerAmount (ModelId.mkPower "PLATING_POWER")) == some 7 &&
  (csPot2.findCreature 200).map (·.getPowerAmount (ModelId.mkPower "DOOM_POWER")) == some 33

def tl_14_tier2_monster_ascension_scaling : Bool :=
  let mkInit (asc : Nat) : CombatState :=
    let cP1 : Creature :=
      { id := 101, modelId := ModelId.mkCharacter "IRONCLAD", side := .player, playerId := some 1
      , currentHp := 80, maxHp := 80 }
    let cE1 : Creature :=
      { id := 200, modelId := ModelId.mkMonster "CALCIFIED_CULTIST", side := .enemy
      , currentHp := 40, maxHp := 40
      , monster := some { modelId := ModelId.mkMonster "CALCIFIED_CULTIST", currentMoveId := "INCANTATION_MOVE" } }
    let p1 : Player :=
      { playerId := 1, creatureId := 101, characterId := ModelId.mkCharacter "IRONCLAD"
      , combatState := some { energy := 3, baseMaxEnergy := 3 } }
    { combatId := 1, roundNumber := 1, currentSide := .player, isInProgress := true
    , ascensionLevel := asc, allies := [cP1], enemies := [cE1], players := [p1], nextInstanceId := 500 }
  -- Round 1: INCANTATION_MOVE applies Ritual 2 (skipped at R1 end); Round 2: DARK_STRIKE_MOVE deals 9 at A0 vs 11 at A9
  let (a0R1, _, _, _, _) := execEnemyTurnHeadless fullVanillaEffectEnv (mkInit 0)
  let (a0R2, _, _, _, _) := execEnemyTurnHeadless fullVanillaEffectEnv a0R1
  let (a9R1, _, _, _, _) := execEnemyTurnHeadless fullVanillaEffectEnv (mkInit AscensionLevel.deadlyEnemies.toNat)
  let (a9R2, _, _, _, _) := execEnemyTurnHeadless fullVanillaEffectEnv a9R1
  (a0R2.findCreature 101).map (·.currentHp) == some (80 - 9) &&
  (a9R2.findCreature 101).map (·.currentHp) == some (80 - 11) &&
  (a9R2.findCreature 200).map (·.getPowerAmount (ModelId.mkPower "STRENGTH_POWER")) == some 2

def allTimelineTests : List (String × Bool) :=
  [ ("tl_01_concurrent_queues_player_choice_pause_resume", tl_01_concurrent_queues_player_choice_pause_resume)
  , ("tl_02_early_resume_buffered_before_pause", tl_02_early_resume_buffered_before_pause)
  , ("tl_03_keyframe_seek_matches_full_replay_and_checksum", tl_03_keyframe_seek_matches_full_replay_and_checksum)
  , ("tl_04_viewer_switch_invariance", tl_04_viewer_switch_invariance)
  , ("tl_05_potion_and_monster_ai_turn_cycle", tl_05_potion_and_monster_ai_turn_cycle)
  , ("tl_06_opaque_state_delta_fallback", tl_06_opaque_state_delta_fallback)
  , ("tl_07_fork_timeline_matches_prefix_plus_alt", tl_07_fork_timeline_matches_prefix_plus_alt)
  , ("tl_08_trace_json_roundtrip_preserves_seek_and_checksums", tl_08_trace_json_roundtrip_preserves_seek_and_checksums)
  , ("tl_09_trace_json_rejects_unsupported_schema_version", tl_09_trace_json_rejects_unsupported_schema_version)
  , ("tl_10_verify_trace_checksums_detects_tampering", tl_10_verify_trace_checksums_detects_tampering)
  , ("tl_11_lifecycle_debuff_skip_tick_and_poison_doom", tl_11_lifecycle_debuff_skip_tick_and_poison_doom)
  , ("tl_12_lifecycle_thorns_plating_ritual_and_orbs", tl_12_lifecycle_thorns_plating_ritual_and_orbs)
  , ("tl_13_tier2_card_and_potion_effects_and_upgrade", tl_13_tier2_card_and_potion_effects_and_upgrade)
  , ("tl_14_tier2_monster_ascension_scaling", tl_14_tier2_monster_ascension_scaling) ]

end Sts2Model.Examples