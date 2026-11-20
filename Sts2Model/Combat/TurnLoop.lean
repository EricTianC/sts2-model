/-
  CombatManager turn state machine: turn setup, two-phase player turn end,
  hand flush & Retain, Ethereal exhaust, enemy turn execution, extra turns,
  and PendingLoss / ShouldStopCombatFromEnding win-condition checks.
  Reference: `reference/sts2/MegaCrit.Sts2.Core.Combat/CombatManager.cs`
-/
import Sts2Model.Core.Enums
import Sts2Model.Model.State
import Sts2Model.Hook.Pipeline
import Sts2Model.Command.CreatureCmd
import Sts2Model.Command.CardCmd
import Sts2Model.Command.PowerCmd
import Sts2Model.Combat.GameAction
import Sts2Model.Mechanics.Orbs
import Sts2Model.Mechanics.Necrobinder

namespace Sts2Model.Combat

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook
open Sts2Model.Command
open Sts2Model.Mechanics

/-- Outcome of checking win/loss condition in `CombatManager.CheckWinCondition`. -/
inductive CombatOutcome where
  | ongoing
  | victory
  | defeat
  deriving Repr, DecidableEq, Inhabited

/-- Set `PlayerTurnPhase` for every player in combat. Ref: `CombatManager.SetPhaseForAllPlayers`. -/
def setPhaseForAllPlayers (cs : CombatState) (phase : PlayerTurnPhase) : CombatState :=
  { cs with
    players := cs.players.map fun p =>
      match p.combatState with
      | none     => p
      | some pcs => { p with combatState := some { pcs with phase := phase } } }

def setPlayerPhase (cs : CombatState) (pid : PlayerId) (phase : PlayerTurnPhase) : CombatState :=
  cs.updatePlayer pid fun p =>
    match p.combatState with
    | none     => p
    | some pcs => { p with combatState := some { pcs with phase := phase } }

/-- Ref: `CombatManager.IsCombatEnding(CombatTurnState)`. -/
def isCombatEnding (cs : CombatState) (reg : BehaviorRegistry)
    (modSubscribers : List (ModId × ModelId) := []) : Bool :=
  if !cs.isInProgress then false
  else if cs.pendingLoss.isSome then true
  else if cs.enemies.any (fun e => e.isAlive && e.isPrimaryEnemy) then false
  else !shouldStopCombatFromEnding cs reg modSubscribers

/-- Ref: `CombatManager.CheckWinCondition(CombatTurnState)`.
    Loss (`pendingLoss`) always takes priority over victory; `ShouldStopCombatFromEnding` can block victory. -/
def checkWinCondition (cs : CombatState) (reg : BehaviorRegistry)
    (modSubscribers : List (ModId × ModelId) := []) : CombatState × CombatOutcome :=
  if !cs.isInProgress then (cs, .ongoing)
  else if cs.pendingLoss.isSome then
    let cs' := { cs with
      isInProgress := false
      isEnding := true
      pendingLoss := none }
    (setPhaseForAllPlayers cs' .none, .defeat)
  else if isCombatEnding cs reg modSubscribers then
    let cs' := { cs with
      isInProgress := false
      isEnding := true }
    (setPhaseForAllPlayers cs' .none, .victory)
  else
    (cs, .ongoing)

/-- Check if all players are dead and mark `pendingLoss` if so. -/
def checkAllPlayersDead (cs : CombatState) : CombatState :=
  if cs.isInProgress && cs.players.all (fun p =>
      match cs.findCreature p.creatureId with
      | some c => c.isDead
      | none   => true) then
    { cs with pendingLoss := cs.pendingLoss.orElse (fun _ => some ⟨0⟩) }
  else cs

/-- Start-of-turn block clear respecting `ShouldClearBlock` (skipped on Player Turn 1).
    Ref: `Creature.AfterTurnStart(CombatSide)` (`Creature.cs` lines 685-696). -/
def clearTurnStartBlock (cs : CombatState) (reg : BehaviorRegistry) (side : CombatSide)
    (modSubscribers : List (ModId × ModelId) := []) : CombatState :=
  let targets := cs.getTeammatesOf side
  targets.foldl (fun (acc : CombatState) (c : Creature) =>
    let isPlayerTurn1 : Bool :=
      match (c.playerId.bind acc.findPlayer).bind (·.combatState) with
      | some pcs => side == .player && pcs.turnNumber == 1
      | none     => false
    if isPlayerTurn1 = true then acc
    else if (shouldClearBlock acc reg c modSubscribers).1 then
      acc.updateCreature c.id (fun cr => { cr with block := 0 })
    else acc) cs

/-- Setup player turn: reset energy (if `ShouldPlayerResetEnergy`), draw 5 cards, transition to `AutoPrePlay` then `Play`.
    Ref: `CombatManager.SetupPlayerTurn` & `StartTurn`. -/
def setupPlayerTurn (cs : CombatState) (reg : BehaviorRegistry) (pid : PlayerId)
    (baseDraw : Nat := 5) (modSubscribers : List (ModId × ModelId) := []) : CombatState :=
  match cs.findPlayer pid with
  | none => cs
  | some original =>
      if !cs.isInProgress then cs
      else
        let cs1 := setPlayerPhase cs pid .start
        let cs2 := cs1.updatePlayer pid fun p =>
          match p.combatState with
          | none => p
          | some pcs =>
              let energy' := if shouldPlayerResetEnergy cs1 reg p modSubscribers then pcs.baseMaxEnergy
                             else (pcs.gainEnergy pcs.baseMaxEnergy).energy
              { p with combatState := some { pcs with energy := energy', playedTagsThisTurn := [] } }
        let (beforeDraw, draws) :=
          match original.combatState with
          | some pcs =>
              if cs.shuffleRng.isSome && pcs.turnNumber == 1 then
                let goesLast := fun (c : CardInstance) => c.enchantment.any (·.modelId == ModelId.mkEnchantment "IMBUED")
                let (bottom, ordinary) := pcs.piles.draw.partition goesLast
                let (innate, middle) := ordinary.partition (·.hasKeyword .innate)
                let next := cs2.updatePlayer pid fun p =>
                  { p with combatState := p.combatState.map fun c =>
                    { c with piles.draw := innate.reverse ++ middle ++ bottom } }
                (next, min PlayerPiles.maxCardsInHand (max baseDraw innate.length))
              else (cs2, baseDraw)
          | none => (cs2, baseDraw)
        let (cs3, _) := drawCards beforeDraw reg pid draws true modSubscribers
        let cs4 := setPlayerPhase cs3 pid .autoPrePlay
        setPlayerPhase cs4 pid .play

/-- Mark player ready to end turn. Ref: `CombatManager.SetReadyToEndTurn`. -/
def setReadyToEndTurn (cs : CombatState) (pid : PlayerId) (canBackOut : Bool := true) : CombatState :=
  let updated :=
    if cs.turnReady.any (·.playerId == pid) then
      cs.turnReady.map fun r =>
        if r.playerId == pid then { r with readyToEnd := true, canBackOut := canBackOut } else r
    else
      cs.turnReady ++ [{ playerId := pid, readyToEnd := true, canBackOut := canBackOut }]
  { cs with turnReady := updated }

/-- Undo ready-to-end-turn if `canBackOut = true`. Ref: `CombatManager.TryUndoReadyToEndTurn`. -/
def tryUndoReadyToEndTurn (cs : CombatState) (pid : PlayerId) : CombatState × Bool :=
  match cs.turnReady.find? (·.playerId == pid) with
  | none => (cs, false)
  | some r =>
      if !r.readyToEnd || !r.canBackOut then (cs, false)
      else
        let updated := cs.turnReady.map fun x =>
          if x.playerId == pid then { x with readyToEnd := false } else x
        ({ cs with turnReady := updated }, true)

def allPlayersReadyToEndTurn (cs : CombatState) : Bool :=
  cs.players.all fun p =>
    cs.turnReady.any fun r => r.playerId == p.playerId && r.readyToEnd

/-- Phase 1 of ending player turn: `AutoPostPlay` -> `End`, exhaust non-exempt `Ethereal` cards in hand.
    Ref: `CombatManager.EndPlayerTurnPhaseOneInternal` & `DoTurnEnd`. -/
def endPlayerTurnPhaseOne (cs : CombatState) (reg : BehaviorRegistry)
    (modSubscribers : List (ModId × ModelId) := []) : CombatState :=
  if !cs.isInProgress || cs.currentSide != .player then cs
  else
    let cs1 := setPhaseForAllPlayers cs .autoPostPlay
    let cs2 := setPhaseForAllPlayers cs1 .«end»
    cs2.players.foldl (fun acc p =>
      match p.combatState with
      | none => acc
      | some pcs =>
          let ethIds := (pcs.piles.hand.filter fun c =>
            c.hasKeyword .ethereal && shouldEtherealTrigger acc reg c modSubscribers).map (·.instanceId)
          ethIds.foldl (fun s cid => exhaustCard s p.playerId cid) acc) cs2

/-- Phase 2 of ending player turn: flush hand to discard (respecting `Retain` and `ShouldFlush`),
    clean up `EndOfTurn` local/temporary cost modifiers, and switch sides (or take extra turn).
    Ref: `CombatManager.EndPlayerTurnPhaseTwoInternal` & `FlushPlayerHand` & `SwitchFromPlayerToEnemySide`. -/
def endPlayerTurnPhaseTwo (cs : CombatState) (reg : BehaviorRegistry)
    (modSubscribers : List (ModId × ModelId) := []) : CombatState :=
  if !cs.isInProgress || cs.currentSide != .player then cs
  else
    let cs1 := cs.players.foldl (fun acc p =>
      match acc.findPlayer p.playerId with
      | none => acc
      | some pl =>
          match pl.combatState with
          | none => acc
          | some pcs =>
              let flushAll := shouldFlush acc reg pl modSubscribers
              let toFlush := (pcs.piles.hand.filter fun c =>
                flushAll && !c.hasKeyword .retain).map (·.instanceId)
              let accFlushed := toFlush.foldl (fun s cid => discardCard s pl.playerId cid) acc
              accFlushed.updatePlayer pl.playerId fun pr =>
                match pr.combatState with
                | none => pr
                | some st =>
                    let cleanList (xs : List CardInstance) := xs.map CardInstance.endOfTurnCleanup
                    let piles' : PlayerPiles :=
                      { draw := cleanList st.piles.draw
                      , hand := cleanList st.piles.hand
                      , discard := cleanList st.piles.discard
                      , exhaust := cleanList st.piles.exhaust
                      , play := cleanList st.piles.play }
                    { pr with combatState := some { st with piles := piles' } }) cs
    let extraTurnPlayers := cs1.players.filter fun p => (shouldTakeExtraTurn cs1 reg p modSubscribers).1
    if !extraTurnPlayers.isEmpty then
      let csExtra := extraTurnPlayers.foldl (fun acc p =>
        acc.updatePlayer p.playerId fun pr =>
          match pr.combatState with
          | none => pr
          | some st => { pr with combatState := some { st with turnNumber := st.turnNumber + 1 } }) cs1
      { csExtra with currentSide := .player, turnReady := [] }
    else
      let csEnemy := { setPhaseForAllPlayers cs1 .none with
        currentSide := .enemy
        turnReady := [] }
      clearTurnStartBlock csEnemy reg .enemy modSubscribers

/-- End enemy turn: clean up & switch back to Player side (`roundNumber + 1`, `turnNumber + 1`).
    Ref: `CombatManager.EndEnemyTurnInternal` & `SwitchSides`. -/
def endEnemyTurn (cs : CombatState) (reg : BehaviorRegistry)
    (modSubscribers : List (ModId × ModelId) := []) : CombatState :=
  if !cs.isInProgress || cs.currentSide != .enemy then cs
  else
    let cs1 := cs.players.foldl (fun acc p =>
      acc.updatePlayer p.playerId fun pr =>
        match pr.combatState with
        | none => pr
        | some st => { pr with combatState := some { st with turnNumber := st.turnNumber + 1 } }) cs
    let cs2 := { cs1 with currentSide := .player, roundNumber := cs1.roundNumber + 1 }
    clearTurnStartBlock cs2 reg .player modSubscribers

/-- Execute a single `GameAction` deterministically on `(CombatState, ActionExecutorState)`.
    Ref: `ActionExecutor.cs` & `PlayCardAction.cs` / `EndPlayerTurnAction.cs`. -/
def executeGameAction (cs : CombatState) (exec : ActionExecutorState) (reg : BehaviorRegistry)
    (act : GameAction)
    (cardEffect : CombatState → CardPlay → CombatState := fun s _ => s)
    (modSubscribers : List (ModId × ModelId) := []) :
    CombatState × ActionExecutorState :=
  if exec.isCanceled || exec.isPaused || !cs.isInProgress then
    (cs, exec)
  else
    let cs' :=
      match act with
      | .playCard pid cid tid =>
          (playCard cs reg pid cid tid cardEffect modSubscribers).1
      | .usePotion _ _ _ => cs
      | .discardPotion pid slotIdx =>
          cs.updatePlayer pid fun p =>
            let pots' := p.potions.zipIdx.map fun (opt, idx) => if idx == slotIdx then none else opt
            { p with potions := pots' }
      | .endPlayerTurn pid canBackOut =>
          setReadyToEndTurn cs pid canBackOut
      | .undoEndPlayerTurn pid =>
          (tryUndoReadyToEndTurn cs pid).1
      | .readyToBeginEnemyTurn pid =>
          let updated := cs.turnReady.map fun r =>
            if r.playerId == pid then { r with readyForEnemyTurn := true } else r
          { cs with turnReady := updated }
    let csChecked := (checkWinCondition (checkAllPlayersDead cs') reg modSubscribers).1
    (csChecked, { exec with executedCount := exec.executedCount + 1 })

/-- Execute a synchronized sequence of `GameAction`s deterministically. -/
def executeActionQueue (cs : CombatState) (exec : ActionExecutorState) (reg : BehaviorRegistry)
    (queue : ActionQueue)
    (cardEffect : CombatState → CardPlay → CombatState := fun s _ => s)
    (modSubscribers : List (ModId × ModelId) := []) :
    CombatState × ActionExecutorState :=
  queue.foldl (fun (s, e) act => executeGameAction s e reg act cardEffect modSubscribers) (cs, exec)

-- ============================================================================
-- Hook-Driven Side Turn Start / End Lifecycle
-- ============================================================================

/-- Execute pure `HookEffect` instructions emitted by turn-lifecycle hooks. -/
def executeHookEffects (cs : CombatState) (reg : BehaviorRegistry) (effects : List HookEffect)
    (modSubscribers : List (ModId × ModelId) := []) : CombatState :=
  effects.foldl (fun acc eff =>
    match eff with
    | .tickDownDuration oid instId => tickDownDuration acc oid instId
    | .clearSkipDurationTick oid instId => clearSkipDurationTick acc oid instId
    | .decrementPower oid instId =>
        -- PoisonPower.Trigger checks IsAlive after dealing damage.
        if (acc.findCreature oid |>.map (·.isAlive) |>.getD false) then
          decrementPowerById acc oid instId
        else acc
    | .modifyPowerAmount oid instId delta => (modifyPowerAmount acc reg oid instId (Dec.ofInt delta) none modSubscribers).1
    | .applyPowerById tid pid amt pType allowNeg =>
        let tmpl : PowerInstance :=
          { instanceId := 0
          , modelId := pid
          , ownerId := tid
          , powerType := pType
          , stackType := .counter
          , allowNegative := allowNeg }
        (applyPower acc reg tmpl tid (Dec.ofInt amt) (some tid) modSubscribers).1
    | .dealDamage dealerId targetId amt props =>
        (damageSingleTarget acc reg targetId amt props dealerId none .all modSubscribers).1
    | .gainBlock targetId amt props =>
        (gainBlock acc reg targetId amt props none modSubscribers).1
    | .doomKillSide side =>
        triggerSideDoomKill acc reg side modSubscribers) cs

/-- Execute start-of-side-turn hooks (`Poison` tick, `Plating` decay, `Plasma` orbs on player turn).
    Ref: `CombatManager.cs` (`AfterSideTurnStart` + `OrbQueue.AfterTurnStart`). -/
def runSideTurnStartLifecycle (cs : CombatState) (reg : BehaviorRegistry) (side : CombatSide)
    (modSubscribers : List (ModId × ModelId) := []) : CombatState × CombatOutcome :=
  if !cs.isInProgress then (cs, .ongoing)
  else
    let participants := (cs.getTeammatesOf side).filter (·.isAlive) |>.map (·.id)
    let effects := collectAfterSideTurnStartEffects cs reg side participants modSubscribers
    let cs1 := executeHookEffects cs reg effects modSubscribers
    let cs2 :=
      if side == .player then
        cs1.players.foldl (fun acc p => triggerTurnStartOrbs acc reg p.playerId modSubscribers) cs1
      else cs1
    checkWinCondition (checkAllPlayersDead cs2) reg modSubscribers

/-- Execute end-of-side-turn hooks (`Plating` block, `BeforeTurnEnd` orbs, `Doom` execute,
    `Vulnerable`/`Weak`/`Frail` duration tick via `skipNextDurationTick`, `Intangible` decrement, `Ritual`).
    Ref: `CombatManager.cs` (`BeforeSideTurnEnd` + `OrbQueue.BeforeTurnEnd` + `AfterSideTurnEnd`). -/
def runSideTurnEndLifecycle (cs : CombatState) (reg : BehaviorRegistry) (side : CombatSide)
    (modSubscribers : List (ModId × ModelId) := []) : CombatState × CombatOutcome :=
  if !cs.isInProgress then (cs, .ongoing)
  else
    let participants := (cs.getTeammatesOf side).filter (·.isAlive) |>.map (·.id)
    let beforeEffs := collectBeforeSideTurnEndEffects cs reg side participants modSubscribers
    let cs1 := executeHookEffects cs reg beforeEffs modSubscribers
    let cs2 :=
      if side == .player then
        cs1.players.foldl (fun acc p => triggerTurnEndOrbs acc reg p.playerId modSubscribers) cs1
      else cs1
    let (cs3, outcome) := checkWinCondition (checkAllPlayersDead cs2) reg modSubscribers
    if !cs3.isInProgress then (cs3, outcome)
    else
      let afterParticipants := (cs3.getTeammatesOf side).filter (·.isAlive) |>.map (·.id)
      let afterEffs := collectAfterSideTurnEndEffects cs3 reg side afterParticipants modSubscribers
      let cs4 := executeHookEffects cs3 reg afterEffs modSubscribers
      checkWinCondition (checkAllPlayersDead cs4) reg modSubscribers

end Sts2Model.Combat
