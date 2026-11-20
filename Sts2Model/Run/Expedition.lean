import Sts2Model.Run.RunLoop
import Sts2Model.Sim.EffectIR

namespace Sts2Model.Run

open Sts2Model.Multiplayer
open Sts2Model.Core Sts2Model.Model Sts2Model.Combat Sts2Model.Sim

inductive ExpeditionOutcome where
  | victory | defeat | abandoned
  deriving Repr, DecidableEq, Inhabited

inductive ExpeditionPhase where
  | map | room | combat | rewards | nextAct | finalEvent | terminal (outcome : ExpeditionOutcome)
  deriving Repr, DecidableEq, Inhabited

inductive ExpeditionOffer where
  | gold (amount : Nat)
  | cards (options : List CardInstance)
  deriving Repr, DecidableEq, Inhabited

inductive ExpeditionRewardState where
  | pending | skipped | claimed (offer : Nat) (card : Option Nat)
  deriving Repr, DecidableEq, Inhabited

/-- An independent offer or an explicitly linked set; offering three cards is one card reward. -/
inductive ExpeditionReward where
  | independent (offer : ExpeditionOffer) (status : ExpeditionRewardState := .pending)
  | linked (offers : List ExpeditionOffer) (status : ExpeditionRewardState := .pending)
  deriving Repr, DecidableEq, Inhabited

namespace ExpeditionReward

def status : ExpeditionReward → ExpeditionRewardState
  | .independent _ s | .linked _ s => s

def setStatus (r : ExpeditionReward) (s : ExpeditionRewardState) : ExpeditionReward :=
  match r with
  | .independent offer _ => .independent offer s
  | .linked offers _ => .linked offers s

private def select (r : ExpeditionReward) (idx : Nat) : Except String ExpeditionOffer := do
  unless r.status == .pending do throw "reward already resolved"
  match r with
  | .independent offer _ =>
      if idx == 0 then pure offer else throw "independent reward has no such alternative"
  | .linked offers _ =>
      let linked : LinkedRewardSet ExpeditionOffer := { rewards := offers }
      let some offer := (linked.selectIndex idx).2 | throw "linked reward index out of range"
      pure offer
end ExpeditionReward

/-- Scenario input: the already resolved encounter and populated reward list, not RNG predictions. -/
structure ExpeditionEncounter where
  id : ModelId
  enemies : List Creature
  rewards : List ExpeditionReward := []
  resumeParent : Bool := false
  deriving Repr, DecidableEq

inductive ExpeditionCombatInput where
  | playCard (card : CardInstanceId) (target : Option CreatureId := none)
  | usePotion (slot : Nat) (target : Option CreatureId := none)
  | answerCardChoice (player : PlayerId) (choice : Nat) (result : ChoiceResult)
  | endTurn
  deriving Repr, DecidableEq, Inhabited

inductive ExpeditionAction where
  | enterPoint (coord : MapCoord) (resolvedRoom : RoomType)
  | enterSubroom (room : RoomType)
  | leaveRoom
  | startEncounter (encounter : ExpeditionEncounter)
  | restoreRewards (rewards : List ExpeditionReward) (resumeParent : Bool := false)
  | combatInput (input : ExpeditionCombatInput)
  | claimGold (reward : Nat) (offer : Nat := 0)
  | chooseCard (reward card : Nat) (offer : Nat := 0)
  | skipReward (reward : Nat)
  | leaveRewards
  | enterNextAct (map : ActMap)
  | enterFinalEvent
  | confirmVictory
  | abandon
  deriving Repr, DecidableEq

/-- Ordinary single-player run with explicit map/room content. `RunState.players` holds the
    permanent deck and items, never the combat copies. `visited.length` is the current act floor. -/
structure Expedition where
  nav : RunNavigationState
  currentHp : Nat
  maxHp : Nat
  actCount : Nat
  phase : ExpeditionPhase := .map
  parentRooms : List RoomType := []
  combat : Option CombatState := none
  encounter : Option ModelId := none
  rewards : List ExpeditionReward := []
  resumeParent : Bool := false
  nextInstanceId : Nat := 1000
  choiceSync : PlayerChoiceSynchronizer := {}
  pendingCard : Option PendingCardChoice := none
  deriving Repr, DecidableEq

namespace Expedition

private def isCombatRoom (room : RoomType) : Bool :=
  room == .monster || room == .elite || room == .boss

private def roomMatches (point : MapPointType) (room : RoomType) : Bool :=
  match point with
  | .unknown => room == .event || room == .monster || room == .elite || room == .shop || room == .treasure
  | .unassigned => room == .event || room == .map
  | .ancient => room == .event
  | .monster => room == .monster
  | .elite => room == .elite
  | .boss => room == .boss
  | .shop => room == .shop
  | .restSite => room == .restSite
  | .treasure => room == .treasure

private def singlePlayer (s : Expedition) : Except String Player :=
  match s.nav.runState.players with
  | [p] => pure p
  | _ => throw "expedition requires one persistent player"

private def setRoom (s : Expedition) (room : RoomType) : Expedition :=
  { s with nav.runState.currentRoom := room }

private def resolved (s : Expedition) : Expedition :=
  let lastBoss := s.nav.actMap.secondBossPoint.getD s.nav.actMap.bossPoint
  let doneAct := s.nav.runState.currentRoom == .boss && s.nav.currentCoord == lastBoss
  { s.setRoom .map with
    phase := if doneAct then .nextAct else .map
    parentRooms := [], encounter := none, rewards := [], resumeParent := false }

private def resumeParentRoom (s : Expedition) (room : RoomType) (rest : List RoomType) : Expedition :=
  { s.setRoom room with
    phase := .room, parentRooms := rest, encounter := none
    rewards := [], resumeParent := false }

private def enterPoint (s : Expedition) (coord : MapCoord) (room : RoomType) : Except String Expedition := do
  let some point := s.nav.actMap.getPoint coord | throw "map point does not exist"
  unless roomMatches point.pointType room do throw "resolved room does not match map point type"
  if s.nav.visited.isEmpty then
    unless coord == s.nav.actMap.startPoint do throw "first point must be the act start"
    pure { s.setRoom room with
      phase := .room
      nav.currentCoord := coord
      nav.visited := [coord]
      nav.runState.totalFloors := s.nav.runState.totalFloors + 1 }
  else
    if s.nav.visited.contains coord then throw "map point already visited"
    else
      let (next, moved) := enterMapPoint s.nav coord room
      if moved then pure { s with nav := next, phase := .room }
      else throw "map edge does not exist"

private def combatCopy (card : CardInstance) (id : Nat) (pid : PlayerId) : CardInstance :=
  { card with
    instanceId := id, ownerId := pid, isCanonical := false, isDupe := false
    energyCost := { card.energyCost with capturedXValue := 0, localModifiers := [] }
    temporaryStarCost := none, exhaustOnNextPlay := false, affliction := none }

private def acceptCombat (s : Expedition) (cs : CombatState) (outcome : CombatOutcome) : Except String Expedition := do
  if outcome == .ongoing then pure { s with phase := .combat, combat := some cs }
  else
    let persistent ← s.singlePlayer
    let some p := cs.findPlayer persistent.playerId | throw "combat lost its player"
    let some creature := cs.findCreature persistent.creatureId | throw "combat lost the player creature"
    let rs := s.nav.runState
    let rng := rs.rngSet
    let rs' := { rs with
      players := [{ p with combatState := none }]
      rngSet := { rng with
        shuffle := cs.shuffleRng.getD rng.shuffle
        monsterAi := cs.monsterAiRng.getD rng.monsterAi
        combatTargets := cs.rng } }
    let won := outcome == .victory
    pure { s with
      nav.runState := rs', nextInstanceId := cs.nextInstanceId
      currentHp := creature.currentHp, maxHp := creature.maxHp, combat := none
      phase := if won then .rewards else .terminal .defeat
      rewards := if won then s.rewards else [] }

private def startEncounter (env : EffectEnv) (s : Expedition) (e : ExpeditionEncounter) : Except String Expedition := do
  unless isCombatRoom s.nav.runState.currentRoom do throw "not a combat room"
  unless !e.resumeParent || !s.parentRooms.isEmpty do throw "encounter has no parent room to resume"
  unless e.rewards.all (fun r => r.status == .pending) do throw "new encounters require pending rewards"
  let p ← s.singlePlayer
  unless e.enemies.any (fun c => c.isAlive && c.isPrimaryEnemy) do throw "encounter has no living primary enemy"
  let mut seen := [p.creatureId]
  let mut nextId := p.deck.foldl (fun n c => max n (c.instanceId + 1)) s.nextInstanceId
  for c in e.enemies do
    if c.side != .enemy || seen.contains c.id then throw "invalid enemy creature or duplicate creature ID"
    seen := c.id :: seen
    for pow in c.powers do nextId := max nextId (pow.instanceId + 1)
  let deck := p.deck.zipIdx.map fun (card, i) => combatCopy card (nextId + i) p.playerId
  let rs := s.nav.runState
  let (draw, shuffle) := Rng.unstableShuffle deck rs.rngSet.shuffle
  let pCombat : PlayerCombatState :=
    { baseMaxEnergy := p.baseMaxEnergy, piles := { draw := draw }
      orbQueue := { capacity := min OrbQueue.maxCapacity p.baseOrbSlots }
      arrows := List.replicate p.baseArrowSlots {} }
  let pc : Creature :=
    { id := p.creatureId, modelId := p.characterId, side := .player
      playerId := some p.playerId, currentHp := s.currentHp, maxHp := s.maxHp }
  let cs : CombatState :=
    { allies := [pc], enemies := e.enemies, players := [{ p with combatState := some pCombat }]
      modifiers := rs.modifiers, badges := rs.badges, runModels := rs.runModels
      dominion := rs.dominion, ascensionLevel := rs.ascensionLevel, nextInstanceId := nextId + deck.length
      rng := rs.rngSet.combatTargets, shuffleRng := some shuffle, monsterAiRng := some rs.rngSet.monsterAi }
  let ready := setupPlayerTurn cs (env.behaviorReg cs) p.playerId
  let (opened, outcome) := runSideTurnStartLifecycle ready (env.behaviorReg ready) .player
  acceptCombat { s with encounter := some e.id, rewards := e.rewards, resumeParent := e.resumeParent } opened outcome

private def legalTarget (cs : CombatState) (p : Player) (card : CardInstance) (target : Option CreatureId) : Bool :=
  let living := target.bind cs.findCreature |>.filter Creature.isAlive
  match card.targetType with
  | .anyEnemy => living.any fun c => c.side == .enemy && c.isHittableFlag
  | .anyAlly => living.any fun c => c.isPlayer && c.id != p.creatureId
  | .anyPlayer => living.any Creature.isPlayer
  | .osty => living.any fun c => c.petOwnerId == some p.playerId
  | .self => target.isNone || target == some p.creatureId
  | _ => target.isNone

private def unsupportedStrictOp : EffectOp → Bool
  | .applyOpaque _ | .discardChosen .. | .exhaustChosen .. => true
  | _ => false

private def acceptCardResult (s : Expedition) (r : HeadlessCardResult) : Except String Expedition :=
  acceptCombat { s with choiceSync := r.sync, pendingCard := r.pending } r.combat r.outcome

private def combatInput (env : EffectEnv) (s : Expedition) (input : ExpeditionCombatInput) : Except String Expedition := do
  let some cs := s.combat | throw "missing expedition combat"
  let p ← s.singlePlayer
  let some live := cs.findPlayer p.playerId | throw "missing combat player"
  let some pcs := live.combatState | throw "missing player combat state"
  unless cs.isInProgress && cs.currentSide == .player && pcs.phase == .play do throw "not the player play phase"
  if let .answerCardChoice pid id result := input then
    let some pending := s.pendingCard | throw "no pending card choice"
    unless pending.accepts cs pid id result do throw "invalid or unreserved expedition card choice"
    let sync := s.choiceSync.recordChoice pid id result
    let resumed ← resumeCardPlay env cs pending 0 [(pid, id, result)] sync
    return ← acceptCardResult s resumed
  unless s.pendingCard.isNone do throw "a card choice is pending"
  match input with
  | .playCard id target =>
      let some card := pcs.piles.hand.find? (·.instanceId == id) | throw "card instance is not in hand"
      unless legalTarget cs p card target do throw "invalid card target"
      let some ops := env.knownCardEffect card | throw s!"unmodeled card: {card.modelId.entry}"
      if ops.any unsupportedStrictOp then throw s!"unmodeled card operation: {card.modelId.entry}"
      let r := execPlayCardHeadless { env with cardEffect := fun _ => ops }
        cs p.playerId id (if card.targetType == .self then some p.creatureId else target) 0 [] s.choiceSync
      if !r.accepted then throw s!"card cannot be played: {card.modelId.entry}"
      acceptCardResult s r
  | .usePotion slot target =>
      let some pot := live.potions[slot]?.join | throw "empty potion slot"
      let some ops := env.knownPotionEffect pot.modelId | throw s!"unmodeled potion: {pot.modelId.entry}"
      if ops.any unsupportedStrictOp then throw s!"unmodeled potion operation: {pot.modelId.entry}"
      let (next, ok, _, _, _, outcome) := execUsePotionHeadless { env with potionEffect := fun _ => ops }
        cs p.playerId slot target
      if !ok then throw s!"potion cannot be used: {pot.modelId.entry}"
      acceptCombat s next outcome
  | .answerCardChoice .. => throw "no pending card choice"
  | .endTurn =>
      for enemy in cs.enemies do
        let mid := (enemy.monster.map (·.modelId)).getD enemy.modelId
        if enemy.isAlive && (env.monsterBlueprint mid).isNone then throw s!"unmodeled enemy: {mid.entry}"
      let (next, _, _, _, outcome) := execEnemyTurnHeadless env cs
      acceptCombat s next outcome

private def rewardAt (s : Expedition) (i : Nat) : Except String ExpeditionReward := do
  let some r := s.rewards[i]? | throw "reward index out of range"
  pure r

private def settle (s : Expedition) (i : Nat) (r : ExpeditionReward) (status : ExpeditionRewardState) : Expedition :=
  { s with rewards := s.rewards.set i (r.setStatus status) }

/-- The sole transition entry point. An error carries no successor state. -/
def step (env : EffectEnv) (s : Expedition) (action : ExpeditionAction) : Except String Expedition := do
  match s.phase, action with
  | .terminal _, _ => throw "expedition already ended"
  | _, .abandon => pure { s with phase := .terminal .abandoned, combat := none, rewards := [], pendingCard := none }
  | .map, .enterPoint coord room => enterPoint s coord room
  | .room, .enterSubroom room =>
      unless s.nav.runState.currentRoom == .event && isCombatRoom room do throw "invalid combat subroom"
      pure { s.setRoom room with parentRooms := s.nav.runState.currentRoom :: s.parentRooms }
  | .room, .leaveRoom =>
      if isCombatRoom s.nav.runState.currentRoom then throw "combat room is not settled"
      else pure s.resolved
  | .room, .startEncounter e => startEncounter env s e
  | .room, .restoreRewards rewards resume =>
      unless isCombatRoom s.nav.runState.currentRoom && (!resume || !s.parentRooms.isEmpty) do
        throw "invalid restored combat reward boundary"
      pure { s with phase := .rewards, rewards := rewards, resumeParent := resume }
  | .combat, .combatInput input => combatInput env s input
  | .rewards, .claimGold i j =>
      let r ← s.rewardAt i
      match ← r.select j with
      | .gold n => pure { s.settle i r (.claimed j none) with nav.runState.gold := s.nav.runState.gold + n }
      | .cards _ => throw "reward is not gold"
  | .rewards, .chooseCard i k j =>
      let r ← s.rewardAt i
      match ← r.select j with
      | .gold _ => throw "reward is not a card reward"
      | .cards choices =>
          let some card := choices[k]? | throw "card reward index out of range"
          let p ← s.singlePlayer
          let id := p.deck.foldl (fun n c => max n (c.instanceId + 1)) s.nextInstanceId
          let received := { card with instanceId := id, ownerId := p.playerId, isCanonical := false }
          pure { s.settle i r (.claimed j (some k)) with
            nav.runState.players := [{ p with deck := p.deck ++ [received] }], nextInstanceId := id + 1 }
  | .rewards, .skipReward i =>
      let r ← s.rewardAt i
      if r.status == .pending then pure (s.settle i r .skipped) else throw "reward already resolved"
  | .rewards, .leaveRewards =>
      if s.rewards.any (fun r => r.status == .pending) then throw "unresolved combat rewards"
      else if s.resumeParent then
        match s.parentRooms with
        | room :: rest => pure (s.resumeParentRoom room rest)
        | [] => throw "missing parent room"
      else pure s.resolved
  | .nextAct, .enterNextAct map =>
      let next := s.nav.runState.currentActIndex + 1
      unless next < s.actCount do throw "last act is complete; enter the final event"
      pure { s with
        phase := .map, nav.actMap := map, nav.currentCoord := map.startPoint
        nav.visited := [], nav.unknownOdds := s.nav.unknownOdds.resetToBase
        nav.runState.currentActIndex := next }
  | .nextAct, .enterFinalEvent =>
      unless s.nav.runState.currentActIndex + 1 == s.actCount do throw "not the last act"
      pure { s.setRoom .event with phase := .finalEvent }
  | .finalEvent, .confirmVictory => pure { s with phase := .terminal .victory }
  | _, _ => throw "action is not allowed in the current expedition phase"

/-- An invalid destination cannot return a successor, including a dangling child edge. -/
theorem missing_point_rejected (env : EffectEnv) (s : Expedition) (dest : MapCoord) (room : RoomType)
    (phase : s.phase = .map) (missing : s.nav.actMap.getPoint dest = none) :
    s.step env (.enterPoint dest room) = .error "map point does not exist" := by
  simp [step, phase, enterPoint, missing]
  rfl

/-- Entering a legal edge counts exactly one new floor, never the coordinate's row. -/
theorem legal_move_adds_one (env : EffectEnv) (s next : Expedition) (dest : MapCoord) (room : RoomType)
    (point : MapPoint) (phase : s.phase = .map) (found : s.nav.actMap.getPoint dest = some point)
    (compatible : roomMatches point.pointType room = true) (started : s.nav.visited.isEmpty = false)
    (fresh : dest ∉ s.nav.visited) (edge : s.nav.actMap.hasEdge s.nav.currentCoord dest = true)
    (moved : s.step env (.enterPoint dest room) = .ok next) :
    next.nav.runState.totalFloors = s.nav.runState.totalFloors + 1 := by
  simp [step, phase, enterPoint, found, compatible, started, fresh, enterMapPoint, edge] at moved
  change Except.ok _ = Except.ok next at moved
  cases moved
  rfl

/-- Already consumed or skipped offers cannot award gold, even via an alternate index. -/
theorem resolved_gold_rejected (env : EffectEnv) (s : Expedition) (r : ExpeditionReward) (i j : Nat)
    (phase : s.phase = .rewards) (found : s.rewards[i]? = some r)
    (resolved : r.status ≠ .pending) :
    s.step env (.claimGold i j) = .error "reward already resolved" := by
  simp [step, phase, rewardAt, found, ExpeditionReward.select, resolved]
  rfl

/-- Already consumed or skipped offers cannot award a card. -/
theorem resolved_card_rejected (env : EffectEnv) (s : Expedition) (r : ExpeditionReward) (i j k : Nat)
    (phase : s.phase = .rewards) (found : s.rewards[i]? = some r)
    (resolved : r.status ≠ .pending) :
    s.step env (.chooseCard i k j) = .error "reward already resolved" := by
  simp [step, phase, rewardAt, found, ExpeditionReward.select, resolved]
  rfl

end Expedition
end Sts2Model.Run
