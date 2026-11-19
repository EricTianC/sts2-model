/-
  Formal proofs for headless multiplayer replay, concurrent ActionQueueSet scheduling,
  keyframe seek equivalence, timeline forking, and viewer-perspective invariance.
  All theorems proved in Lean 4 kernel with zero `sorry`, zero `axiom`, zero `native_decide`.
-/
import Sts2Model.Replay.Timeline

namespace Sts2Model.Proofs

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Multiplayer
open Sts2Model.Sim
open Sts2Model.Replay

-- ============================================================================
-- 1. ActionQueueSet Scheduling & Concurrency Theorems
-- ============================================================================

theorem actionQueueSet_enqueue_increments_id (qs : ActionQueueSet) (ownerId : PlayerId)
    (actionType : GameActionType) (isPlayerDriven isPlayCard : Bool)
    (payload : ReplayActionPayload) :
    (qs.enqueue ownerId actionType isPlayerDriven isPlayCard payload).1.nextActionId =
      qs.nextActionId + 1 := by
  unfold ActionQueueSet.enqueue
  dsimp only
  split <;> rfl

theorem pickMinIdAction_le_left (a b r : QueuedAction)
    (h : ActionQueueSet.pickMinIdAction (some a) (some b) = some r) :
    r.actionId ≤ a.actionId := by
  simp only [ActionQueueSet.pickMinIdAction] at h
  split at h
  · cases h; omega
  · cases h; exact Nat.le_refl _

theorem pickMinIdAction_le_right (a b r : QueuedAction)
    (h : ActionQueueSet.pickMinIdAction (some a) (some b) = some r) :
    r.actionId ≤ b.actionId := by
  simp only [ActionQueueSet.pickMinIdAction] at h
  split at h
  · cases h; exact Nat.le_refl _
  · cases h; omega

theorem pickMinIdAction_left_some (a : QueuedAction) (b : Option QueuedAction) (r : QueuedAction)
    (h : ActionQueueSet.pickMinIdAction (some a) b = some r) :
    r.actionId ≤ a.actionId := by
  cases b with
  | none =>
      simp only [ActionQueueSet.pickMinIdAction] at h
      cases h
      exact Nat.le_refl _
  | some b' => exact pickMinIdAction_le_left a b' r h

theorem pickBestReady_some_of_eligible (isInCombat : Bool) :
    ∀ (queues : List PlayerActionQueue) (q : PlayerActionQueue) (hd : QueuedAction) (tl : List QueuedAction),
      q ∈ queues → q.actions = hd :: tl →
      ActionQueueSet.isActionEligible isInCombat q.isPaused hd = true →
      ∃ r, ActionQueueSet.pickBestReady isInCombat queues = some r
  | [], _, _, _, hmem, _, _ => nomatch hmem
  | q₀ :: rest, q, hd, tl, hmem, hact, helig => by
      cases List.mem_cons.mp hmem with
      | inl heq =>
          subst heq
          unfold ActionQueueSet.pickBestReady
          rw [hact]
          dsimp only
          rw [helig]
          cases htail : ActionQueueSet.pickBestReady isInCombat rest with
          | none => exact ⟨hd, by simp [ActionQueueSet.pickMinIdAction]⟩
          | some r₀ =>
              by_cases hlt : r₀.actionId < hd.actionId
              · exact ⟨r₀, by simp [ActionQueueSet.pickMinIdAction, hlt]⟩
              · exact ⟨hd, by simp [ActionQueueSet.pickMinIdAction, hlt]⟩
      | inr htail =>
          obtain ⟨r₀, hr₀⟩ := pickBestReady_some_of_eligible isInCombat rest q hd tl htail hact helig
          unfold ActionQueueSet.pickBestReady
          rw [hr₀]
          cases hq₀ : q₀.actions with
          | nil => exact ⟨r₀, rfl⟩
          | cons a₀ as₀ =>
              by_cases hel₀ : ActionQueueSet.isActionEligible isInCombat q₀.isPaused a₀ = true
              · simp only [hel₀, ↓reduceIte, ActionQueueSet.pickMinIdAction]
                split
                · exact ⟨r₀, rfl⟩
                · exact ⟨a₀, rfl⟩
              · have hf : ActionQueueSet.isActionEligible isInCombat q₀.isPaused a₀ = false :=
                  Bool.eq_false_iff.mpr hel₀
                simp [hf]

theorem pickBestReady_le_eligible (isInCombat : Bool) :
    ∀ (queues : List PlayerActionQueue) (res : QueuedAction),
      ActionQueueSet.pickBestReady isInCombat queues = some res →
      ∀ q ∈ queues, ∀ hd tl, q.actions = hd :: tl →
        ActionQueueSet.isActionEligible isInCombat q.isPaused hd = true →
        res.actionId ≤ hd.actionId
  | [], _, h, _, hmem, _, _, _, _ => nomatch hmem
  | q₀ :: rest, res, hPick, q, hmem, hd, tl, hact, helig => by
      cases List.mem_cons.mp hmem with
      | inl heq =>
          subst heq
          unfold ActionQueueSet.pickBestReady at hPick
          rw [hact] at hPick
          dsimp only at hPick
          rw [helig] at hPick
          exact pickMinIdAction_left_some hd (ActionQueueSet.pickBestReady isInCombat rest) res hPick
      | inr htail =>
          obtain ⟨r₀, hr₀⟩ := pickBestReady_some_of_eligible isInCombat rest q hd tl htail hact helig
          have hSubLe : r₀.actionId ≤ hd.actionId :=
            pickBestReady_le_eligible isInCombat rest r₀ hr₀ q htail hd tl hact helig
          unfold ActionQueueSet.pickBestReady at hPick
          cases hq₀ : q₀.actions with
          | nil =>
              rw [hq₀] at hPick
              dsimp only at hPick
              rw [hr₀] at hPick
              cases hPick
              exact hSubLe
          | cons a₀ as₀ =>
              rw [hq₀, hr₀] at hPick
              dsimp only at hPick
              by_cases hel₀ : ActionQueueSet.isActionEligible isInCombat q₀.isPaused a₀ = true
              · simp only [hel₀, ↓reduceIte] at hPick
                exact Nat.le_trans (pickMinIdAction_le_right a₀ r₀ res hPick) hSubLe
              · have hf : ActionQueueSet.isActionEligible isInCombat q₀.isPaused a₀ = false :=
                  Bool.eq_false_iff.mpr hel₀
                simp only [hf, Bool.false_eq_true, ↓reduceIte] at hPick
                cases hPick
                exact hSubLe

/-- `ActionQueueSet.getReadyAction` always picks the eligible head with minimum `actionId`
    across all player queues (matching `ActionQueueSet.cs` lines 184-255). -/
theorem actionQueueSet_getReadyAction_is_min_id (qs : ActionQueueSet) (qs' : ActionQueueSet)
    (res : QueuedAction) (hReady : qs.getReadyAction = (qs', some res)) :
    ∀ q ∈ qs'.queues, ∀ hd tl, q.actions = hd :: tl →
      ActionQueueSet.isActionEligible qs'.isInCombat q.isPaused hd = true →
      res.actionId ≤ hd.actionId := by
  unfold ActionQueueSet.getReadyAction at hReady
  have hfst := congrArg Prod.fst hReady
  have hsnd := congrArg Prod.snd hReady
  dsimp only at hfst hsnd
  subst hfst
  exact pickBestReady_le_eligible qs.isInCombat _ res hsnd

/-- Pausing Player 1's head action for a `PlayerChoice` leaves Player 2's queue
    unblocked and selectable by `getReadyAction`. -/
theorem actionQueueSet_pause_blocks_only_owner
    (p1 p2 : PlayerId) (id1 id2 : Nat) (pl1 pl2 : ReplayActionPayload)
    (hAid : id1 ≠ id2) :
    let a1 : QueuedAction :=
      { actionId := id1, ownerId := p1, actionType := .combatPlayPhaseOnly
      , isPlayerDriven := true, isPlayCard := true, state := .waitingForExecution, payload := pl1 }
    let a2 : QueuedAction :=
      { actionId := id2, ownerId := p2, actionType := .combatPlayPhaseOnly
      , isPlayerDriven := true, isPlayCard := true, state := .waitingForExecution, payload := pl2 }
    let qs : ActionQueueSet :=
      { queues :=
          [ { ownerId := p1, actions := [a1], isCancellingCombatActions := false, isPaused := false }
          , { ownerId := p2, actions := [a2], isCancellingCombatActions := false, isPaused := false } ]
      , nextActionId := max id1 id2 + 1
      , isInCombat := true }
    let (qsPaused, pausedOk) := qs.pauseActionForPlayerChoice id1 {}
    pausedOk = true ∧ (qsPaused.getReadyAction).2 = some a2 := by
  have hne21 : id2 ≠ id1 := hAid.symm
  simp [ActionQueueSet.pauseActionForPlayerChoice, ActionQueueSet.takeWaitingResumption,
        ActionQueueSet.getReadyAction, ActionQueueSet.cleanCanceledHead,
        ActionQueueSet.pickBestReady, ActionQueueSet.isActionEligible,
        ActionQueueSet.pickMinIdAction, hne21]

/-- Early `resumeAction` arriving before `pauseActionForPlayerChoice` is buffered in
    `waitingForResumption` and immediately applied upon pausing, assigning `newId = nxt`. -/
theorem actionQueueSet_early_resume_buffered_and_applied
    (p1 : PlayerId) (aid nxt : Nat) (pl : ReplayActionPayload) :
    let act : QueuedAction :=
      { actionId := aid, ownerId := p1, actionType := .combatPlayPhaseOnly
      , isPlayerDriven := true, isPlayCard := true, state := .executing, payload := pl }
    let qs : ActionQueueSet :=
      { queues := [{ ownerId := p1, actions := [act], isCancellingCombatActions := false }]
      , nextActionId := nxt, isInCombat := true }
    let (qs1, newId) := qs.resumeAction aid
    let (qs2, pausedOk) := qs1.pauseActionForPlayerChoice aid {}
    newId = nxt ∧ pausedOk = true ∧ qs2.waitingForResumption = [] ∧
    (qs2.getReadyAction).2 = some { act with actionId := nxt, state := .readyToResumeExecuting } := by
  simp [ActionQueueSet.resumeAction, ActionQueueSet.pauseActionForPlayerChoice,
        ActionQueueSet.takeWaitingResumption, ActionQueueSet.getReadyAction,
        ActionQueueSet.cleanCanceledHead, ActionQueueSet.pickBestReady,
        ActionQueueSet.isActionEligible, ActionQueueSet.pickMinIdAction]

-- ============================================================================
-- 2. Replay Prefix Equivalence & Keyframe Seek Exactness
-- ============================================================================

theorem replayEvents_nil (env : EffectEnv) (st : TimelineState) :
    replayEvents env st [] = st := rfl

theorem replayEvents_append (env : EffectEnv) (st : TimelineState) (e₁ e₂ : List TimelineEvent) :
    replayEvents env st (e₁ ++ e₂) = replayEvents env (replayEvents env st e₁) e₂ := by
  unfold replayEvents
  simp [List.foldl_append]

theorem list_take_split {α : Type} :
    ∀ (j : Nat) (xs : List α) (k : Nat), j ≤ k →
      xs.take k = xs.take j ++ (xs.drop j).take (k - j)
  | 0, xs, k, _ => by simp
  | j + 1, [], k, _ => by simp
  | j + 1, _ :: _, 0, hjk => by omega
  | j + 1, _ :: tl, k + 1, hjk => by
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      congr 1
      simpa [Nat.succ_sub_succ] using list_take_split j tl k (by omega)

/-- Every keyframe stores the exact state produced by replaying from `initialState`
    through its recorded prefix `events.take kf.eventIndex`. -/
def ValidKeyframes (env : EffectEnv) (archive : TimelineArchive) : Prop :=
  ∀ kf ∈ archive.keyframes,
    kf.eventIndex ≤ archive.events.length ∧
    kf.state = replayEvents env archive.initialState (archive.events.take kf.eventIndex)

theorem buildKeyframesLoop_inv (env : EffectEnv) (init : TimelineState) (stride : Nat) :
    ∀ (rem pref : List TimelineEvent) (accKfs : List Keyframe),
      (∀ kf ∈ accKfs,
        kf.eventIndex ≤ pref.length ∧
        kf.state = replayEvents env init ((pref ++ rem).take kf.eventIndex)) →
      ∀ kf ∈ buildKeyframesLoop env stride pref.length (replayEvents env init pref) rem accKfs,
        kf.eventIndex ≤ (pref ++ rem).length ∧
        kf.state = replayEvents env init ((pref ++ rem).take kf.eventIndex)
  | [], pref, accKfs, hAcc => by
      simpa [buildKeyframesLoop] using hAcc
  | ev :: rest, pref, accKfs, hAcc => by
      have hAssoc : pref ++ ev :: rest = (pref ++ [ev]) ++ rest := by
        simp [List.append_assoc]
      have hNextState :
          replayStep env (replayEvents env init pref) ev =
            replayEvents env init (pref ++ [ev]) := by
        rw [replayEvents_append]
        rfl
      have hPrevInv :
          ∀ kf ∈ accKfs,
            kf.eventIndex ≤ (pref ++ [ev]).length ∧
            kf.state = replayEvents env init (((pref ++ [ev]) ++ rest).take kf.eventIndex) := by
        intro kf hmem
        have h1 := hAcc kf hmem
        refine ⟨by simp; omega, ?_⟩
        rw [← hAssoc]
        exact h1.2
      unfold buildKeyframesLoop
      dsimp only
      split
      · have hNewInv :
            ∀ kf ∈ accKfs ++
                [{ eventIndex := pref.length + 1
                 , state := replayStep env (replayEvents env init pref) ev
                 , checksum := computeStateChecksum (replayStep env (replayEvents env init pref) ev) }],
              kf.eventIndex ≤ (pref ++ [ev]).length ∧
              kf.state = replayEvents env init (((pref ++ [ev]) ++ rest).take kf.eventIndex) := by
          intro kf hmem
          cases List.mem_append.mp hmem with
          | inl hOld => exact hPrevInv kf hOld
          | inr hNew =>
              simp only [List.mem_singleton] at hNew
              subst hNew
              dsimp only
              refine ⟨by simp, ?_⟩
              have hLen : (pref ++ [ev]).length = pref.length + 1 := by simp
              have hTake : ((pref ++ [ev]) ++ rest).take (pref.length + 1) = pref ++ [ev] := by
                rw [← hLen]
                exact List.take_left
              rw [hTake]
              exact hNextState
        have hSubEq : (pref ++ [ev]).length = pref.length + 1 := by simp
        have hSub :=
          buildKeyframesLoop_inv env init stride rest (pref ++ [ev])
            (accKfs ++ [{ eventIndex := pref.length + 1
                        , state := replayStep env (replayEvents env init pref) ev
                        , checksum := computeStateChecksum (replayStep env (replayEvents env init pref) ev) }])
            hNewInv
        rw [hSubEq, ← hNextState] at hSub
        intro kf hmem
        have hk := hSub kf hmem
        rw [hAssoc]
        exact hk
      · have hSubEq : (pref ++ [ev]).length = pref.length + 1 := by simp
        have hSub :=
          buildKeyframesLoop_inv env init stride rest (pref ++ [ev]) accKfs hPrevInv
        rw [hSubEq, ← hNextState] at hSub
        intro kf hmem
        have hk := hSub kf hmem
        rw [hAssoc]
        exact hk

/-- Any archive created by `buildArchive` unconditionally satisfies `ValidKeyframes`. -/
theorem buildArchive_validKeyframes (env : EffectEnv) (init : TimelineState)
    (evs : List TimelineEvent) (stride : Nat) (viewer : PlayerId) :
    ValidKeyframes env (buildArchive env init evs stride viewer) := by
  unfold ValidKeyframes buildArchive
  dsimp only
  have hBase :
      ∀ kf : Keyframe, kf ∈ [{ eventIndex := 0, state := init, checksum := computeStateChecksum init }] →
        kf.eventIndex ≤ ([] : List TimelineEvent).length ∧
        kf.state = replayEvents env init (([] ++ evs).take kf.eventIndex) := by
    intro kf hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    simp [replayEvents]
  have hRes := buildKeyframesLoop_inv env init (max 1 stride) evs []
    [{ eventIndex := 0, state := init, checksum := computeStateChecksum init }] hBase
  simpa [replayEvents] using hRes

theorem foldl_selectKeyframeStep_spec (targetIdx : Nat) (P : Keyframe → Prop) :
    ∀ (kfs : List Keyframe) (best : Option Keyframe),
      (∀ kf ∈ kfs, P kf) →
      (∀ b, best = some b → P b ∧ b.eventIndex ≤ targetIdx) →
      ∀ kf, kfs.foldl (selectKeyframeStep targetIdx) best = some kf →
        P kf ∧ kf.eventIndex ≤ targetIdx
  | [], best, _, hBest, kf, hFold => by
      simp only [List.foldl_nil] at hFold
      exact hBest kf hFold
  | x :: xs, best, hAll, hBest, kf, hFold => by
      simp only [List.foldl_cons] at hFold
      refine foldl_selectKeyframeStep_spec targetIdx P xs (selectKeyframeStep targetIdx best x)
        (fun y hy => hAll y (List.mem_cons_of_mem x hy)) ?_ kf hFold
      intro b hb
      unfold selectKeyframeStep at hb
      split at hb
      · rename_i hle
        cases best with
        | none =>
            cases hb
            exact ⟨hAll x (List.mem_cons_self ..), hle⟩
        | some prev =>
            dsimp only at hb
            split at hb
            · cases hb
              exact ⟨hAll x (List.mem_cons_self ..), hle⟩
            · cases hb
              exact hBest b rfl
      · exact hBest b hb

/-- Core correctness guarantee for timeline scrubbing / random access:
    seeking to any step `k` via keyframes yields the exact same state as replaying
    from the very start (`0 .. k`). -/
theorem keyframe_seek_exact_equivalence (env : EffectEnv) (archive : TimelineArchive)
    (hValid : ValidKeyframes env archive) (k : Nat) :
    seek env archive k = replayEvents env archive.initialState (archive.events.take k) := by
  unfold seek findNearestKeyframe
  cases hNearest : archive.keyframes.foldl (selectKeyframeStep k) none with
  | none => rfl
  | some kf =>
      have hSpec := foldl_selectKeyframeStep_spec k (fun y => y ∈ archive.keyframes)
        archive.keyframes none (fun y hy => hy) (fun _ h => nomatch h) kf hNearest
      have hV := hValid kf hSpec.1
      have hKfState : kf.state = replayEvents env archive.initialState (archive.events.take kf.eventIndex) :=
        hV.2
      have hKfLeK : kf.eventIndex ≤ k := hSpec.2
      dsimp only
      rw [hKfState, ← replayEvents_append, ← list_take_split kf.eventIndex archive.events k hKfLeK]

/-- Under valid keyframes, forking an archive at `branchIdx` and replaying `altEvents`
    yields the exact same state as replaying `events.take branchIdx ++ altEvents` from `0`. -/
theorem forkTimeline_exact_equivalence (env : EffectEnv) (archive : TimelineArchive)
    (hValid : ValidKeyframes env archive) (branchIdx : Nat) (altEvents : List TimelineEvent) :
    forkTimeline env archive branchIdx altEvents =
      replayEvents env archive.initialState (archive.events.take branchIdx ++ altEvents) := by
  unfold forkTimeline
  rw [keyframe_seek_exact_equivalence env archive hValid branchIdx, replayEvents_append]

/-- Switching the player perspective (`viewerPlayerId`) does not alter any shared state or checksum. -/
theorem viewer_switch_preserves_seek_and_checksum (env : EffectEnv) (archive : TimelineArchive)
    (v : PlayerId) (k : Nat) :
    seek env (switchViewer archive v) k = seek env archive k ∧
    computeStateChecksum (seek env (switchViewer archive v) k) =
      computeStateChecksum (seek env archive k) :=
  ⟨rfl, rfl⟩

end Sts2Model.Proofs
