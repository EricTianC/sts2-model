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

def allTimelineTests : List (String × Bool) :=
  [ ("tl_01_concurrent_queues_player_choice_pause_resume", tl_01_concurrent_queues_player_choice_pause_resume)
  , ("tl_02_early_resume_buffered_before_pause", tl_02_early_resume_buffered_before_pause)
  , ("tl_03_keyframe_seek_matches_full_replay_and_checksum", tl_03_keyframe_seek_matches_full_replay_and_checksum)
  , ("tl_04_viewer_switch_invariance", tl_04_viewer_switch_invariance)
  , ("tl_05_potion_and_monster_ai_turn_cycle", tl_05_potion_and_monster_ai_turn_cycle)
  , ("tl_06_opaque_state_delta_fallback", tl_06_opaque_state_delta_fallback) ]

end Sts2Model.Examples