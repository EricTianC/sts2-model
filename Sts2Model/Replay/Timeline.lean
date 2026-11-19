/-
  Headless multiplayer Timeline Archive, 64-bit FNV-1a State Checksums,
  Keyframe Seek engine, out-of-combat Run sync events, and viewer perspective switching.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Multiplayer.Replay/CombatReplay.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Multiplayer.Replay/CombatReplayEvent.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Multiplayer.Replay/CombatReplayEventType.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Multiplayer.Replay/CombatReplayWriter.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Multiplayer.Game/ChecksumTracker.cs`
-/
import Sts2Model.Sim.EffectIR
import Sts2Model.Run.RunLoop

namespace Sts2Model.Replay

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Combat
open Sts2Model.Multiplayer
open Sts2Model.Run
open Sts2Model.Sim

/-- Four recordable combat replay event types + `none` matching `CombatReplayEventType.cs`. -/
inductive CombatReplayEventType where
  | none
  | gameAction
  | hookAction
  | resumeAction
  | playerChoice
  deriving Repr, DecidableEq, Inhabited

/-- Structured replay event matching `CombatReplayEvent.cs`. -/
structure CombatReplayEvent where
  eventType    : CombatReplayEventType
  playerId     : Option PlayerId := none
  payload      : Option ReplayActionPayload := none
  hookId       : Option Nat := none
  actionId     : Option Nat := none
  choiceId     : Option Nat := none
  choiceResult : Option ChoiceResult := none
  deriving Repr, DecidableEq, Inhabited

/-- Out-of-combat run-level synchronized events across map, events, merchant, rest, rewards, and acts. -/
inductive OutOfCombatSyncEvent where
  | mapVote (row col : Nat)
  | mapMove (row col : Nat) (pointType : MapPointType) (roomType : RoomType)
  | eventChoice (optionKey : String) (goldDelta : Int := 0) (hpDelta : Int := 0)
  | merchantBuy (cardModel : Option ModelId) (goldCost : Nat)
  | restSiteHeal (healAmt : Nat)
  | rewardPick (cardModel : Option ModelId) (goldGain : Nat := 0)
  | treasureRelicPick (relicId : ModelId) (rarity : RelicRarity := .common)
  | actAdvance
  deriving Repr, DecidableEq, Inhabited

/-- Unified timeline event tagged across combat, concurrent pauses, turn transitions,
    out-of-combat run progression, and unmodeled opaque deltas. -/
inductive TimelineEventKind where
  | combat (ev : CombatReplayEvent)
  | pauseActionForChoice (actionId : Nat) (opts : PlayerChoiceOptions := {})
  | endRoundAndRunEnemies
  | runSync (ev : OutOfCombatSyncEvent)
  | opaqueStep (delta : OpaqueStateDelta)
  deriving Repr, DecidableEq

/-- Timestamped headless timeline entry (`Act / Floor / Round / Actor`). -/
structure TimelineEvent where
  seqIdx        : Nat
  actIndex      : Nat := 0
  floor         : Nat := 1
  roundNumber   : Nat := 1
  actorPlayerId : PlayerId := 1
  kind          : TimelineEventKind
  deriving Repr, DecidableEq

/-- Exact synchronization ID counters stored in keyframe / initial replay snapshots.
    Ref: `CombatReplayWriter.cs` lines 66-72. -/
structure SyncCounters where
  nextActionId   : Nat := 0
  nextHookId     : Nat := 0
  nextChecksumId : Nat := 0
  choiceIds      : List (PlayerId × Nat) := []
  rewardIds      : List Nat := []
  modelIdHash    : UInt32 := 0
  deriving Repr, DecidableEq, Inhabited

/-- Complete deterministic shared world state at any timeline point (viewer-agnostic). -/
structure TimelineState where
  runState         : RunState := {}
  combat           : Option CombatState := none
  queueSet         : ActionQueueSet := {}
  choiceSync       : PlayerChoiceSynchronizer := {}
  counters         : SyncCounters := {}
  choiceStream     : ChoiceStream := []
  combatHistory    : List TimedCombatHistoryEntry := []
  runHistory       : List RunHistoryEntryEx := []
  attributions     : List DamageAttribution := []
  deriving Repr, DecidableEq, Inhabited

-- ============================================================================
-- Deterministic 64-bit FNV-1a Canonical State Checksum
-- ============================================================================

def fnvOffsetBasis : UInt64 := 14695981039346656037
def fnvPrime : UInt64 := 1099511628211

@[inline] def fnv1aByte (h : UInt64) (b : UInt8) : UInt64 :=
  (h ^^^ b.toUInt64) * fnvPrime

def fnv1aUInt64 (h v : UInt64) : UInt64 :=
  let b0 := UInt8.ofNat (v &&& 0xFF).toNat
  let b1 := UInt8.ofNat ((v >>> 8) &&& 0xFF).toNat
  let b2 := UInt8.ofNat ((v >>> 16) &&& 0xFF).toNat
  let b3 := UInt8.ofNat ((v >>> 24) &&& 0xFF).toNat
  let b4 := UInt8.ofNat ((v >>> 32) &&& 0xFF).toNat
  let b5 := UInt8.ofNat ((v >>> 40) &&& 0xFF).toNat
  let b6 := UInt8.ofNat ((v >>> 48) &&& 0xFF).toNat
  let b7 := UInt8.ofNat ((v >>> 56) &&& 0xFF).toNat
  let h0 := fnv1aByte h b0
  let h1 := fnv1aByte h0 b1
  let h2 := fnv1aByte h1 b2
  let h3 := fnv1aByte h2 b3
  let h4 := fnv1aByte h3 b4
  let h5 := fnv1aByte h4 b5
  let h6 := fnv1aByte h5 b6
  fnv1aByte h6 b7

@[inline] def fnv1aNat (h : UInt64) (n : Nat) : UInt64 :=
  fnv1aUInt64 h (UInt64.ofNat n)

@[inline] def fnv1aInt (h : UInt64) (x : Int) : UInt64 :=
  let h1 := fnv1aByte h (if x < 0 then 1 else 0)
  fnv1aNat h1 x.natAbs

def fnv1aString (h : UInt64) (s : String) : UInt64 :=
  let cs := s.toList
  let h1 := fnv1aNat h cs.length
  cs.foldl (fun acc c => fnv1aByte acc (UInt8.ofNat (c.toNat % 256))) h1

def combatSideCode : CombatSide → Nat
  | .none   => 0
  | .player => 1
  | .enemy  => 2

def fnv1aCreature (h : UInt64) (c : Creature) : UInt64 :=
  let h1 := fnv1aNat h c.id
  let h2 := fnv1aNat h1 c.currentHp
  let h3 := fnv1aNat h2 c.maxHp
  let h4 := fnv1aNat h3 c.block
  let h5 := fnv1aNat h4 c.powers.length
  c.powers.foldl (fun acc p =>
    let a1 := fnv1aString acc p.modelId.entry
    fnv1aInt a1 p.amount) h5

def fnv1aPlayerCards (h : UInt64) (p : Player) : UInt64 :=
  let h1 := fnv1aNat h p.playerId
  let h2 := fnv1aNat h1 p.potions.length
  match p.combatState with
  | none => fnv1aByte h2 0
  | some pcs =>
      let h3 := fnv1aByte h2 1
      let h4 := fnv1aNat h3 pcs.energy
      let h5 := fnv1aNat h4 pcs.stars
      let h6 := fnv1aNat h5 pcs.piles.hand.length
      let h7 := fnv1aNat h6 pcs.piles.draw.length
      let h8 := fnv1aNat h7 pcs.piles.discard.length
      let h9 := fnv1aNat h8 pcs.piles.exhaust.length
      let cards := pcs.piles.hand ++ pcs.piles.draw ++ pcs.piles.discard
      cards.foldl (fun acc c =>
        let a1 := fnv1aNat acc c.instanceId
        fnv1aString a1 c.modelId.entry) h9

def computeCombatChecksum (cs : CombatState) (h : UInt64 := fnvOffsetBasis) : UInt64 :=
  let h1 := fnv1aNat h cs.combatId
  let h2 := fnv1aNat h1 cs.roundNumber
  let h3 := fnv1aNat h2 (combatSideCode cs.currentSide)
  let h4 := fnv1aByte h3 (if cs.isInProgress then 1 else 0)
  let h5 := fnv1aByte h4 (if cs.isEnding then 1 else 0)
  let h6 := fnv1aNat h5 cs.rng.counter
  let h7 := fnv1aUInt64 h6 cs.rng.state.s0
  let h8 := fnv1aUInt64 h7 cs.rng.state.s1
  let h9 := fnv1aUInt64 h8 cs.rng.state.s2
  let h10 := fnv1aUInt64 h9 cs.rng.state.s3
  let h11 := fnv1aNat h10 cs.nextInstanceId
  let creatures := cs.allies ++ cs.enemies
  let h12 := fnv1aNat h11 creatures.length
  let h13 := creatures.foldl fnv1aCreature h12
  let h14 := fnv1aNat h13 cs.players.length
  cs.players.foldl fnv1aPlayerCards h14

/-- Compute deterministic 64-bit checksum of shared `TimelineState`
    (deliberately independent of `viewerPlayerId`). -/
def computeStateChecksum (st : TimelineState) : UInt64 :=
  let h1 := fnv1aUInt64 fnvOffsetBasis st.runState.runSeed
  let h2 := fnv1aNat h1 st.runState.currentActIndex
  let h3 := fnv1aNat h2 st.runState.gold
  let h4 := fnv1aNat h3 st.runState.totalFloors
  let h5 := fnv1aNat h4 st.queueSet.nextActionId
  let h6 := fnv1aNat h5 st.queueSet.nextHookId
  let h7 := fnv1aByte h6 (if st.queueSet.isInCombat then 1 else 0)
  let h8 := fnv1aNat h7 st.queueSet.canceledCount
  let h9 := fnv1aNat h8 st.counters.nextChecksumId
  match st.combat with
  | none    => fnv1aByte h9 0
  | some cs => computeCombatChecksum cs (fnv1aByte h9 1)

-- ============================================================================
-- Replay Engine & Keyframe Archive
-- ============================================================================

structure Keyframe where
  eventIndex : Nat
  state      : TimelineState
  checksum   : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- Headless multi-player replay archive with periodic keyframes and selectable perspective. -/
structure TimelineArchive where
  initialState   : TimelineState
  events         : List TimelineEvent := []
  keyframes      : List Keyframe := []
  viewerPlayerId : PlayerId := 1
  deriving Repr, DecidableEq, Inhabited

def payloadMeta : ReplayActionPayload → GameActionType × Bool × Bool
  | .playCard _ _            => (.combatPlayPhaseOnly, true, true)
  | .usePotion _ _           => (.combatPlayPhaseOnly, true, false)
  | .discardPotion _         => (.combatPlayPhaseOnly, true, false)
  | .endPlayerTurn _         => (.combatPlayPhaseOnly, true, false)
  | .undoEndPlayerTurn       => (.combatPlayPhaseOnly, true, false)
  | .readyToBeginEnemyTurn   => (.combat, false, false)
  | .hookAction _            => (.combat, false, false)
  | .voteMapCoord _ _        => (.nonCombat, true, false)
  | .moveMapCoord _ _        => (.nonCombat, true, false)
  | .pickRelic _             => (.nonCombat, true, false)
  | .voteNextAct             => (.nonCombat, true, false)

def execQueuedActionHeadless (env : EffectEnv) (st : TimelineState) (stepIdx : Nat)
    (act : QueuedAction) : TimelineState :=
  match st.combat with
  | none => st
  | some cs =>
      match act.payload with
      | .playCard cid tid =>
          let (cs', _, hist, attrs, stream') :=
            execPlayCardHeadless env cs act.ownerId cid tid stepIdx st.choiceStream
          { st with
            combat := some cs'
            choiceStream := stream'
            combatHistory := st.combatHistory ++ hist.map (fun e => { stepIdx := stepIdx, entry := e })
            attributions := st.attributions ++ attrs }
      | .usePotion slotIdx tid =>
          let (cs', _, hist, attrs, stream') :=
            execUsePotionHeadless env cs act.ownerId slotIdx tid stepIdx st.choiceStream
          { st with
            combat := some cs'
            choiceStream := stream'
            combatHistory := st.combatHistory ++ hist.map (fun e => { stepIdx := stepIdx, entry := e })
            attributions := st.attributions ++ attrs }
      | .discardPotion slotIdx =>
          let cs' := cs.updatePlayer act.ownerId fun p =>
            { p with potions := p.potions.zipIdx.map fun (opt, idx) => if idx == slotIdx then none else opt }
          { st with combat := some cs' }
      | .endPlayerTurn canBackOut =>
          let cs' := setReadyToEndTurn cs act.ownerId canBackOut
          { st with combat := some cs' }
      | .undoEndPlayerTurn =>
          let (cs', _) := tryUndoReadyToEndTurn cs act.ownerId
          { st with combat := some cs' }
      | .readyToBeginEnemyTurn =>
          let updated := cs.turnReady.map fun r =>
            if r.playerId == act.ownerId then { r with readyForEnemyTurn := true } else r
          { st with combat := some { cs with turnReady := updated } }
      | .hookAction _ | .voteMapCoord _ _ | .moveMapCoord _ _ | .pickRelic _ | .voteNextAct => st

/-- Bounded queue drain: repeatedly pick minimum-ID eligible head action via
    `ActionQueueSet.getReadyAction`, mark executing, apply headless command, and pop. -/
def drainReadyQueueFuel (fuel : Nat) (env : EffectEnv) (stepIdx : Nat)
    (st : TimelineState) : TimelineState :=
  match fuel with
  | 0 => st
  | k + 1 =>
      let (qs1, readyOpt) := st.queueSet.getReadyAction
      match readyOpt with
      | none => { st with queueSet := qs1 }
      | some act =>
          let qsExec := qs1.beginExecuting act.actionId
          let stExec := execQueuedActionHeadless env { st with queueSet := qsExec } stepIdx act
          let qsPopped := stExec.queueSet.popAction act.actionId
          drainReadyQueueFuel k env stepIdx { stExec with queueSet := qsPopped }

def applyOutOfCombatSync (st : TimelineState) (ev : TimelineEvent)
    (sync : OutOfCombatSyncEvent) : TimelineState :=
  let rs := st.runState
  match sync with
  | .mapVote _ _ => st
  | .mapMove _ _ pt rt =>
      let rs' := { rs with currentRoom := rt, totalFloors := rs.totalFloors + 1 }
      let h1 := RunHistoryEntryEx.mapPoint ev.actIndex ev.floor pt 1
      let h2 := RunHistoryEntryEx.mapPointRoom ev.actIndex ev.floor rt none []
      { st with runState := rs', runHistory := st.runHistory ++ [h1, h2] }
  | .eventChoice optKey goldDelta hpDelta =>
      let rs' := { rs with gold := applyIntDeltaClamped rs.gold goldDelta Creature.statCap }
      let rsHp := { rs' with
        players := rs'.players.map fun p =>
          if p.playerId != ev.actorPlayerId then p else p }
      let _ := hpDelta
      let h := RunHistoryEntryEx.eventOption ev.actIndex ev.floor ev.actorPlayerId optKey
      { st with runState := rsHp, runHistory := st.runHistory ++ [h] }
  | .merchantBuy cardOpt goldCost =>
      let rs' := { rs with gold := rs.gold - min rs.gold goldCost }
      let rsDeck :=
        match cardOpt with
        | none => rs'
        | some mid =>
            { rs' with
              players := rs'.players.map fun p =>
                if p.playerId != ev.actorPlayerId then p
                else
                  let newCard : CardInstance :=
                    { instanceId := 80000 + ev.seqIdx
                    , modelId := mid
                    , ownerId := p.playerId
                    , cardType := .skill
                    , rarity := .common
                    , targetType := .self
                    , energyCost := CardEnergyCost.mkCanonical 1 }
                  { p with deck := p.deck ++ [newCard] } }
      let h := RunHistoryEntryEx.blitzMerchant ev.actIndex ev.floor ev.actorPlayerId cardOpt true
      { st with runState := rsDeck, runHistory := st.runHistory ++ [h] }
  | .restSiteHeal _ =>
      { st with runHistory := st.runHistory ++ [.modelChoice ev.actIndex ev.floor ev.actorPlayerId (ModelId.mkModifier "REST_HEAL") true] }
  | .rewardPick cardOpt goldGain =>
      let rs' := { rs with gold := rs.gold + goldGain }
      let h :=
        match cardOpt with
        | some mid => [RunHistoryEntryEx.cardChoice ev.actIndex ev.floor ev.actorPlayerId mid true]
        | none => []
      { st with runState := rs', runHistory := st.runHistory ++ h }
  | .treasureRelicPick relicId rarity =>
      let rs' :=
        { rs with
          players := rs.players.map fun p =>
            if p.playerId != ev.actorPlayerId then p
            else { p with relics := p.relics ++ [{ modelId := relicId, rarity := rarity }] } }
      let h := RunHistoryEntryEx.modelChoice ev.actIndex ev.floor ev.actorPlayerId relicId true
      { st with runState := rs', runHistory := st.runHistory ++ [h] }
  | .actAdvance =>
      let rs' := { rs with currentActIndex := rs.currentActIndex + 1, currentRoom := .unassigned }
      { st with runState := rs' }

def totalQueuedCount (qs : ActionQueueSet) : Nat :=
  qs.queues.foldl (fun acc q => acc + q.actions.length) 0

def bumpCounters (st : TimelineState) : TimelineState :=
  { st with
    counters :=
      { st.counters with
        nextActionId := st.queueSet.nextActionId
        nextHookId := st.queueSet.nextHookId
        nextChecksumId := st.counters.nextChecksumId + 1
        choiceIds := st.choiceSync.nextChoiceIds } }

/-- Advance `TimelineState` deterministically by one `TimelineEvent`. -/
def replayStep (env : EffectEnv) (st : TimelineState) (ev : TimelineEvent) : TimelineState :=
  let stNext :=
    match ev.kind with
    | .combat ce =>
        match ce.eventType with
        | .none => st
        | .gameAction =>
            let pid := ce.playerId.getD ev.actorPlayerId
            match ce.payload with
            | none => st
            | some pl =>
                let (atp, pDriven, isPlayCard) := payloadMeta pl
                let (qs1, _, _) := st.queueSet.enqueue pid atp pDriven isPlayCard pl
                let fuel := totalQueuedCount qs1 + 4
                drainReadyQueueFuel fuel env ev.seqIdx { st with queueSet := qs1 }
        | .hookAction =>
            let hid := ce.hookId.getD st.queueSet.nextHookId
            let qs1 := { st.queueSet with nextHookId := max st.queueSet.nextHookId (hid + 1) }
            let pid := ce.playerId.getD ev.actorPlayerId
            let (qs2, _, _) := qs1.enqueue pid .combat false false (.hookAction hid)
            drainReadyQueueFuel (totalQueuedCount qs2 + 4) env ev.seqIdx { st with queueSet := qs2 }
        | .resumeAction =>
            match ce.actionId with
            | none => st
            | some oldId =>
                let (qs1, _) := st.queueSet.resumeAction oldId
                drainReadyQueueFuel (totalQueuedCount qs1 + 4) env ev.seqIdx { st with queueSet := qs1 }
        | .playerChoice =>
            let pid := ce.playerId.getD ev.actorPlayerId
            let cid := ce.choiceId.getD 0
            let res := ce.choiceResult.getD .skipped
            let sync' := st.choiceSync.recordChoice pid cid res
            { st with
              choiceSync := sync'
              choiceStream := st.choiceStream ++ [(pid, cid, res)] }
    | .pauseActionForChoice aid opts =>
        let (qs1, _) := st.queueSet.pauseActionForPlayerChoice aid opts
        { st with queueSet := qs1 }
    | .endRoundAndRunEnemies =>
        match st.combat with
        | none => st
        | some cs =>
            let (cs', mHist, mAttrs, stream') :=
              execEnemyTurnHeadless env cs ev.seqIdx st.choiceStream
            { st with
              combat := some cs'
              choiceStream := stream'
              combatHistory := st.combatHistory ++ mHist.map (fun e => { stepIdx := ev.seqIdx, entry := e })
              attributions := st.attributions ++ mAttrs }
    | .runSync rEv => applyOutOfCombatSync st ev rEv
    | .opaqueStep delta =>
        match st.combat with
        | none => st
        | some cs => { st with combat := some (applyOpaqueDelta cs delta) }
  bumpCounters stNext

def replayEvents (env : EffectEnv) (st : TimelineState) (evs : List TimelineEvent) : TimelineState :=
  evs.foldl (replayStep env) st

/-- Helper loop collecting periodic keyframes while advancing state across events. -/
def buildKeyframesLoop (env : EffectEnv) (stride : Nat) (idx : Nat) (curState : TimelineState)
    (rem : List TimelineEvent) (accKfs : List Keyframe) : List Keyframe :=
  match rem with
  | [] => accKfs
  | ev :: rest =>
      let nextIdx := idx + 1
      let nextState := replayStep env curState ev
      let accKfs' :=
        if nextIdx % stride == 0 then
          accKfs ++ [{ eventIndex := nextIdx, state := nextState, checksum := computeStateChecksum nextState }]
        else accKfs
      buildKeyframesLoop env stride nextIdx nextState rest accKfs'

/-- Build a `TimelineArchive` with an initial keyframe at index `0` and periodic keyframes
    every `max 1 keyframeStride` steps. -/
def buildArchive (env : EffectEnv) (init : TimelineState) (evs : List TimelineEvent)
    (keyframeStride : Nat := 4) (viewer : PlayerId := 1) : TimelineArchive :=
  let stride := max 1 keyframeStride
  let kf0 : Keyframe := { eventIndex := 0, state := init, checksum := computeStateChecksum init }
  { initialState := init
  , events := evs
  , keyframes := buildKeyframesLoop env stride 0 init evs [kf0]
  , viewerPlayerId := viewer }

def selectKeyframeStep (targetIdx : Nat) (best : Option Keyframe) (kf : Keyframe) : Option Keyframe :=
  if kf.eventIndex ≤ targetIdx then
    match best with
    | none   => some kf
    | some b => if b.eventIndex ≤ kf.eventIndex then some kf else some b
  else best

/-- Find the keyframe with largest `eventIndex ≤ targetIdx`. -/
def findNearestKeyframe (kfs : List Keyframe) (targetIdx : Nat) : Option Keyframe :=
  kfs.foldl (selectKeyframeStep targetIdx) none

/-- Jump to any arbitrary timeline position `targetIdx` by resuming from the nearest keyframe
    instead of replaying from event `0`. -/
def seek (env : EffectEnv) (archive : TimelineArchive) (targetIdx : Nat) : TimelineState :=
  match findNearestKeyframe archive.keyframes targetIdx with
  | none => replayEvents env archive.initialState (archive.events.take targetIdx)
  | some kf =>
      let slice := (archive.events.drop kf.eventIndex).take (targetIdx - kf.eventIndex)
      replayEvents env kf.state slice

/-- Generic timeline fork: seek to `branchIdx` and replay an alternative event suffix
    without prescribing any application-specific comparison metric. -/
def forkTimeline (env : EffectEnv) (archive : TimelineArchive)
    (branchIdx : Nat) (altEvents : List TimelineEvent) : TimelineState :=
  replayEvents env (seek env archive branchIdx) altEvents

/-- Switch the inspection perspective (`playerId`) cleanly without altering shared state. -/
def switchViewer (archive : TimelineArchive) (newViewer : PlayerId) : TimelineArchive :=
  { archive with viewerPlayerId := newViewer }

/-- Render a clean headless text summary of every timeline step (zero UI / animation assets). -/
def formatTimelineSummary (env : EffectEnv) (archive : TimelineArchive) : String :=
  let rec renderSteps (idx : Nat) (rem : List TimelineEvent) (lines : List String) : List String :=
    match rem with
    | [] => lines
    | _ :: rest =>
        let stepNum := idx + 1
        let st : TimelineState := seek env archive stepNum
        let csum := computeStateChecksum st
        let stateDesc :=
          match st.combat with
          | none =>
              s!"[Run] Act={st.runState.currentActIndex} Floor={st.runState.totalFloors} Gold={st.runState.gold} Viewer=P{archive.viewerPlayerId}"
          | some cs =>
              let eStr := String.intercalate ", " (cs.enemies.map fun (e : Creature) =>
                s!"{e.modelId.entry}(id={e.id}):HP={e.currentHp}/{e.maxHp},Blk={e.block},Pow={e.powers.length}")
              let pStr := String.intercalate ", " (cs.players.map fun (p : Player) =>
                let eng := (p.combatState.map PlayerCombatState.energy).getD 0
                let strs := (p.combatState.map PlayerCombatState.stars).getD 0
                s!"P{p.playerId}:E={eng},S={strs}")
              s!"[Combat R{cs.roundNumber} Viewer=P{archive.viewerPlayerId}] {pStr} | Enemies=[{eStr}]"
        renderSteps stepNum rest (lines ++ [s!"  Step #{stepNum}: {stateDesc} | Checksum=0x{String.ofList (Nat.toDigits 16 csum.toNat)}"])
  String.intercalate "\n" (renderSteps 0 archive.events [])

end Sts2Model.Replay
