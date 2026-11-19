/-
  Multiplayer concurrent ActionQueueSet and PlayerChoiceSynchronizer modeling.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Actions/GameActionState.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Multiplayer/GameActionType.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Multiplayer/PlayerChoiceOptions.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.GameActions.Multiplayer/ActionQueueSet.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.GameActions.Multiplayer/PlayerChoiceSynchronizer.cs`
-/
import Sts2Model.Core.Ids
import Sts2Model.Model.State

namespace Sts2Model.Multiplayer

open Sts2Model.Core
open Sts2Model.Model

/-- Execution lifecycle of a `GameAction`. Ref: `Core.Entities.Actions/GameActionState.cs`. -/
inductive GameActionState where
  | none
  | waitingForExecution
  | executing
  | gatheringPlayerChoice
  | readyToResumeExecuting
  | finished
  | canceled
  deriving Repr, DecidableEq, Inhabited

/-- Synchronization & cancellation category of a `GameAction`.
    Ref: `Core.Entities.Multiplayer/GameActionType.cs`. -/
inductive GameActionType where
  | none
  | combat
  | combatPlayPhaseOnly
  | nonCombat
  | any
  deriving Repr, DecidableEq, Inhabited

/-- Options passed when pausing an action for a player choice.
    Ref: `Core.Entities.Multiplayer/PlayerChoiceOptions.cs`. -/
structure PlayerChoiceOptions where
  cancelPlayCardActions : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Serializable player decision carried inside `ChoiceStream` / `PlayerChoice` events.
    Ref: `Core.Entities.Multiplayer/NetPlayerChoiceResult.cs`. -/
inductive ChoiceResult where
  | cards (ids : List CardInstanceId)
  | creature (cid : CreatureId)
  | index (idx : Nat)
  | skipped
  deriving Repr, DecidableEq, Inhabited

/-- Concrete deterministic action payload replicated across multiplayer peers.
    Ref: `Core.GameActions/*.cs` and `CombatReplayEvent.cs`. -/
inductive ReplayActionPayload where
  | playCard (cardId : CardInstanceId) (targetId : Option CreatureId)
  | usePotion (slotIdx : Nat) (targetId : Option CreatureId)
  | discardPotion (slotIdx : Nat)
  | endPlayerTurn (canBackOut : Bool := true)
  | undoEndPlayerTurn
  | readyToBeginEnemyTurn
  | hookAction (hookId : Nat)
  | voteMapCoord (row col : Nat)
  | moveMapCoord (row col : Nat)
  | pickRelic (relicId : ModelId)
  | voteNextAct
  deriving Repr, DecidableEq, Inhabited

/-- An action instance stored inside a player's `PlayerActionQueue`. -/
structure QueuedAction where
  actionId       : Nat
  ownerId        : PlayerId
  actionType     : GameActionType
  isPlayerDriven : Bool := true
  isPlayCard     : Bool := false
  state          : GameActionState := .waitingForExecution
  payload        : ReplayActionPayload
  deriving Repr, DecidableEq, Inhabited

/-- Per-player FIFO action queue and local cancellation flags.
    Ref: `ActionQueueSet.ActionQueue` (`ActionQueueSet.cs`). -/
structure PlayerActionQueue where
  ownerId                             : PlayerId
  actions                             : List QueuedAction := []
  cancellingPlayCardActionId          : Option Nat := none
  isCancellingPlayerDrivenCombatActions : Bool := false
  isCancellingCombatActions           : Bool := true
  isPaused                            : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Resumption token buffered when `ResumeActionWithoutSynchronizing` arrives
    before the local peer finishes reaching `PauseActionForPlayerChoice`.
    Ref: `ActionQueueSet.ActionWaitingForResumption`. -/
structure ActionWaitingForResumption where
  oldId : Nat
  newId : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Multi-player concurrent action queue set preserving global deterministic ordering
    via monotonically increasing `nextActionId` and non-blocking cross-player progress
    when one player's queue is paused on a `PlayerChoice`.
    Ref: `Core.GameActions.Multiplayer/ActionQueueSet.cs`. -/
structure ActionQueueSet where
  queues               : List PlayerActionQueue := []
  waitingForResumption : List ActionWaitingForResumption := []
  nextActionId         : Nat := 0
  nextHookId           : Nat := 0
  isInCombat           : Bool := false
  wasReset             : Bool := false
  canceledCount        : Nat := 0
  deriving Repr, DecidableEq, Inhabited

namespace ActionQueueSet

/-- Initialize one `PlayerActionQueue` per player in deterministic player order. -/
def init (players : List PlayerId) (nextActionId : Nat := 0) (nextHookId : Nat := 0) :
    ActionQueueSet :=
  { queues := players.map (fun pid => { ownerId := pid })
  , waitingForResumption := []
  , nextActionId := nextActionId
  , nextHookId := nextHookId
  , isInCombat := false
  , wasReset := false
  , canceledCount := 0 }

def setUpForCombat (qs : ActionQueueSet) : ActionQueueSet :=
  { qs with
    wasReset := false
    isInCombat := false
    queues := qs.queues.map fun q => { q with isCancellingCombatActions := false } }

def combatStarted (qs : ActionQueueSet) : ActionQueueSet :=
  { qs with
    isInCombat := true
    wasReset := false
    queues := qs.queues.map fun q => { q with isCancellingCombatActions := false } }

def pauseAllPlayerQueues (qs : ActionQueueSet) : ActionQueueSet :=
  { qs with
    queues := qs.queues.map fun q =>
      { q with isPaused := true, isCancellingPlayerDrivenCombatActions := false } }

def unpauseAllPlayerQueues (qs : ActionQueueSet) : ActionQueueSet :=
  { qs with
    queues := qs.queues.map fun q =>
      { q with isPaused := false, isCancellingPlayerDrivenCombatActions := false } }

/-- Strip canceled actions from the front of a queue. Ref: `ActionQueueSet.GetReadyAction` line 195. -/
def cleanCanceledHead : List QueuedAction → List QueuedAction
  | [] => []
  | a :: rest => if a.state == .canceled then cleanCanceledHead rest else a :: rest

/-- Eligibility predicate matching `ActionQueueSet.GetReadyAction` lines 205-235. -/
def isActionEligible (isInCombat : Bool) (qPaused : Bool) (a : QueuedAction) : Bool :=
  if a.state == .canceled then false
  else if isInCombat && a.actionType == .nonCombat then false
  else if !isInCombat && (a.actionType == .combat || a.actionType == .combatPlayPhaseOnly) then false
  else if qPaused && a.actionType == .combatPlayPhaseOnly then false
  else if a.state == .gatheringPlayerChoice then false
  else a.state == .waitingForExecution || a.state == .readyToResumeExecuting

def pickMinIdAction : Option QueuedAction → Option QueuedAction → Option QueuedAction
  | none, b => b
  | a, none => a
  | some a, some b => if b.actionId < a.actionId then some b else some a

/-- Helper folding across queues after canceled heads have been stripped. -/
def pickBestReady (isInCombat : Bool) : List PlayerActionQueue → Option QueuedAction
  | [] => none
  | q :: rest =>
      let tailBest := pickBestReady isInCombat rest
      match q.actions with
      | [] => tailBest
      | head :: _ =>
          if isActionEligible isInCombat q.isPaused head then
            pickMinIdAction (some head) tailBest
          else
            tailBest

/-- Strip canceled heads from all queues, then select the eligible head action with
    minimum `actionId` across all players. Ref: `ActionQueueSet.GetReadyAction`. -/
def getReadyAction (qs : ActionQueueSet) : ActionQueueSet × Option QueuedAction :=
  let cleanedQueues := qs.queues.map fun q => { q with actions := cleanCanceledHead q.actions }
  let qs' := { qs with queues := cleanedQueues }
  (qs', pickBestReady qs'.isInCombat cleanedQueues)

/-- Enqueue a new action directly to `ownerId`'s queue, assigning `nextActionId` and applying
    the three cancellation guards from `ActionQueueSet.EnqueueWithoutSynchronizing`.
    Returns `(updatedQueueSet, assignedId, accepted)`. -/
def enqueue (qs : ActionQueueSet) (ownerId : PlayerId) (actionType : GameActionType)
    (isPlayerDriven : Bool) (isPlayCard : Bool) (payload : ReplayActionPayload) :
    ActionQueueSet × Nat × Bool :=
  let assignedId := qs.nextActionId
  let nextId' := assignedId + 1
  if !(qs.queues.any (·.ownerId == ownerId)) then
    ({ qs with nextActionId := nextId' }, assignedId, false)
  else
    let newAct : QueuedAction :=
      { actionId := assignedId
      , ownerId := ownerId
      , actionType := actionType
      , isPlayerDriven := isPlayerDriven
      , isPlayCard := isPlayCard
      , state := .waitingForExecution
      , payload := payload }
    let (queues', canceledHere) := qs.queues.foldr (fun q (acc, cCnt) =>
      if q.ownerId != ownerId then
        (q :: acc, cCnt)
      else
        let cancelForChoice := q.cancellingPlayCardActionId.isSome && isPlayCard
        let cancelForEndTurn := q.isCancellingPlayerDrivenCombatActions && isPlayerDriven &&
          actionType != .nonCombat && actionType != .any
        let cancelForCombatEnd := q.isCancellingCombatActions &&
          (actionType == .combat || actionType == .combatPlayPhaseOnly)
        if cancelForChoice || cancelForEndTurn || cancelForCombatEnd then
          (q :: acc, cCnt + 1)
        else
          ({ q with actions := q.actions ++ [newAct] } :: acc, cCnt)) ([], 0)
    let accepted := canceledHere == 0
    ({ qs with
       queues := queues'
       nextActionId := nextId'
       canceledCount := qs.canceledCount + canceledHere }, assignedId, accepted)

/-- Mark the action with `actionId` as `.executing` if currently eligible at head. -/
def beginExecuting (qs : ActionQueueSet) (actionId : Nat) : ActionQueueSet :=
  { qs with
    queues := qs.queues.map fun q =>
      match q.actions with
      | head :: rest =>
          if head.actionId == actionId then
            { q with actions := { head with state := .executing } :: rest }
          else q
      | [] => q }

def takeWaitingResumption (oldId : Nat) :
    List ActionWaitingForResumption → Option ActionWaitingForResumption × List ActionWaitingForResumption
  | [] => (none, [])
  | r :: rest =>
      if r.oldId == oldId then (some r, rest)
      else
        let (found, rem) := takeWaitingResumption oldId rest
        (found, r :: rem)

def cancelWaitingPlayCardsInList (maxActionId : Option Nat) :
    List QueuedAction → List QueuedAction × Nat
  | [] => ([], 0)
  | a :: rest =>
      let (restKept, restCanceled) := cancelWaitingPlayCardsInList maxActionId rest
      let shouldCancel := a.isPlayCard && a.state == .waitingForExecution &&
        match maxActionId with
        | none => true
        | some m => a.actionId < m
      if shouldCancel then (restKept, restCanceled + 1)
      else (a :: restKept, restCanceled)

/-- Pause head action `actionId` for a player choice. Handles buffered early resumptions
    and `PlayerChoiceOptions.cancelPlayCardActions`. Ref: `ActionQueueSet.PauseActionForPlayerChoice`. -/
def pauseActionForPlayerChoice (qs : ActionQueueSet) (actionId : Nat)
    (opts : PlayerChoiceOptions := {}) : ActionQueueSet × Bool :=
  let isHeadAnywhere := qs.queues.any fun q =>
    match q.actions with
    | head :: _ => head.actionId == actionId
    | [] => false
  if !isHeadAnywhere then (qs, false)
  else
    let (earlyResume, remainingWaiting) := takeWaitingResumption actionId qs.waitingForResumption
    let maxId := earlyResume.map (·.newId)
    let (queues', canceledAdded) := qs.queues.foldr (fun q (acc, cCnt) =>
      match q.actions with
      | head :: rest =>
          if head.actionId != actionId then (q :: acc, cCnt)
          else
            let headPaused := { head with state := .gatheringPlayerChoice }
            let (rest', newlyCanceled) :=
              if opts.cancelPlayCardActions then cancelWaitingPlayCardsInList maxId rest
              else (rest, 0)
            let qAfterPause : PlayerActionQueue :=
              { q with
                actions := headPaused :: rest'
                cancellingPlayCardActionId :=
                  if opts.cancelPlayCardActions then some actionId else q.cancellingPlayCardActionId }
            let qFinal :=
              match earlyResume with
              | none => qAfterPause
              | some res =>
                  { qAfterPause with
                    actions := { headPaused with actionId := res.newId, state := .readyToResumeExecuting } :: rest'
                    cancellingPlayCardActionId := none }
            (qFinal :: acc, cCnt + newlyCanceled)
      | [] => (q :: acc, cCnt)) ([], 0)
    ({ qs with
       queues := queues'
       waitingForResumption := remainingWaiting
       canceledCount := qs.canceledCount + canceledAdded }, true)

/-- Resume action `oldId` after receiving a `PlayerChoice`, assigning a fresh monotonic `newId`.
    If the action is not yet in `.gatheringPlayerChoice`, buffers `(oldId, newId)` in
    `waitingForResumption`. Ref: `ActionQueueSet.ResumeActionWithoutSynchronizing`. -/
def resumeAction (qs : ActionQueueSet) (oldId : Nat) : ActionQueueSet × Nat :=
  let newId := qs.nextActionId
  let qsNext := { qs with nextActionId := newId + 1 }
  let foundGathering := qsNext.queues.any fun q =>
    q.actions.any fun a => a.actionId == oldId && a.state == .gatheringPlayerChoice
  if foundGathering then
    let queues' := qsNext.queues.map fun q =>
      let hasOld := q.actions.any fun a => a.actionId == oldId && a.state == .gatheringPlayerChoice
      if !hasOld then q
      else
        { q with
          cancellingPlayCardActionId := none
          actions := q.actions.map fun a =>
            if a.actionId == oldId && a.state == .gatheringPlayerChoice then
              { a with actionId := newId, state := .readyToResumeExecuting }
            else a }
    ({ qsNext with queues := queues' }, newId)
  else
    ({ qsNext with
       waitingForResumption := qsNext.waitingForResumption ++ [{ oldId := oldId, newId := newId }] }, newId)

/-- Pop a finished head action `actionId` from its owner's queue. Ref: `ActionQueueSet.PopAction`. -/
def popAction (qs : ActionQueueSet) (actionId : Nat) : ActionQueueSet :=
  { qs with
    queues := qs.queues.map fun q =>
      match q.actions with
      | head :: rest =>
          if head.actionId == actionId then
            { q with
              actions := rest
              cancellingPlayCardActionId :=
                if q.cancellingPlayCardActionId == some actionId then none
                else q.cancellingPlayCardActionId }
          else q
      | [] => q }

def startCancellingAllPlayerDrivenCombatActions (qs : ActionQueueSet) : ActionQueueSet :=
  let (queues', canceledAdded) := qs.queues.foldr (fun q (acc, cCnt) =>
    let (kept, remCnt) := q.actions.foldr (fun a (kAcc, kCnt) =>
      let cancel := a.isPlayerDriven && a.actionType != .nonCombat && a.actionType != .any &&
        a.state == .waitingForExecution
      if cancel then (kAcc, kCnt + 1) else (a :: kAcc, kCnt)) ([], 0)
    ({ q with isCancellingPlayerDrivenCombatActions := true, actions := kept } :: acc, cCnt + remCnt)) ([], 0)
  { qs with queues := queues', canceledCount := qs.canceledCount + canceledAdded }

def combatEnded (qs : ActionQueueSet) : ActionQueueSet :=
  let (queues', canceledAdded) := qs.queues.foldr (fun q (acc, cCnt) =>
    let (kept, remCnt) := q.actions.foldr (fun a (kAcc, kCnt) =>
      let cancel := (a.actionType == .combat || a.actionType == .combatPlayPhaseOnly) &&
        a.state != .executing
      if cancel then (kAcc, kCnt + 1) else (a :: kAcc, kCnt)) ([], 0)
    ({ q with
       actions := kept
       cancellingPlayCardActionId := none
       isCancellingPlayerDrivenCombatActions := false
       isCancellingCombatActions := true } :: acc, cCnt + remCnt)) ([], 0)
  { qs with isInCombat := false, queues := queues', canceledCount := qs.canceledCount + canceledAdded }

def fastForwardNextActionId (qs : ActionQueueSet) (nextId : Nat) : ActionQueueSet :=
  { qs with nextActionId := nextId }

end ActionQueueSet

/-- Per-player monotonic choice ID reservations & recorded results.
    Ref: `Core.GameActions.Multiplayer/PlayerChoiceSynchronizer.cs`. -/
structure PlayerChoiceSynchronizer where
  nextChoiceIds   : List (PlayerId × Nat) := []
  recordedChoices : List (PlayerId × Nat × ChoiceResult) := []
  deriving Repr, DecidableEq, Inhabited

/-- Oracle stream of player choices consumed deterministically during headless replay. -/
abbrev ChoiceStream := List (PlayerId × Nat × ChoiceResult)

namespace PlayerChoiceSynchronizer

def init (players : List PlayerId) : PlayerChoiceSynchronizer :=
  { nextChoiceIds := players.map (·, 0), recordedChoices := [] }

def getChoiceId (s : PlayerChoiceSynchronizer) (pid : PlayerId) : Nat :=
  match s.nextChoiceIds.find? (·.1 == pid) with
  | some (_, n) => n
  | none => 0

def reserveChoiceId (s : PlayerChoiceSynchronizer) (pid : PlayerId) : PlayerChoiceSynchronizer × Nat :=
  let cur := s.getChoiceId pid
  let hasEntry := s.nextChoiceIds.any (·.1 == pid)
  let updated :=
    if hasEntry then
      s.nextChoiceIds.map fun (p, n) => if p == pid then (p, cur + 1) else (p, n)
    else
      s.nextChoiceIds ++ [(pid, cur + 1)]
  ({ s with nextChoiceIds := updated }, cur)

def recordChoice (s : PlayerChoiceSynchronizer) (pid : PlayerId) (choiceId : Nat)
    (res : ChoiceResult) : PlayerChoiceSynchronizer :=
  { s with recordedChoices := s.recordedChoices ++ [(pid, choiceId, res)] }

/-- Deterministically look up & consume a peer choice matching `(pid, choiceId)` from `stream`. -/
def consumeFromStream (pid : PlayerId) (choiceId : Nat) :
    ChoiceStream → Option ChoiceResult × ChoiceStream
  | [] => (none, [])
  | (p, cid, res) :: rest =>
      if p == pid && cid == choiceId then (some res, rest)
      else
        let (found, rem) := consumeFromStream pid choiceId rest
        (found, (p, cid, res) :: rem)

end PlayerChoiceSynchronizer

end Sts2Model.Multiplayer
