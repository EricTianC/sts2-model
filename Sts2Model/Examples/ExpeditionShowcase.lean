import Sts2Model.Run.Expedition
import Sts2Model.Sim.VanillaEffects

namespace Sts2Model.Examples

open Sts2Model.Core Sts2Model.Model Sts2Model.Run Sts2Model.Sim

private def start : MapCoord := ⟨3, 0⟩
private def roomA : MapCoord := ⟨2, 1⟩
private def roomB : MapCoord := ⟨2, 2⟩
private def boss : MapCoord := ⟨3, 3⟩
private def secondBoss : MapCoord := ⟨3, 4⟩
private def dangling : MapCoord := ⟨4, 2⟩

private def map1 : ActMap :=
  { startPoint := start, bossPoint := boss, secondBossPoint := some secondBoss
    points := [⟨start, .ancient, [roomA]⟩, ⟨roomA, .monster, [roomB, dangling]⟩,
      ⟨roomB, .monster, [boss]⟩, ⟨boss, .boss, [secondBoss]⟩, ⟨secondBoss, .boss, []⟩] }

private def map2 : ActMap :=
  { startPoint := start, bossPoint := boss
    points := [⟨start, .ancient, [boss]⟩, ⟨boss, .boss, []⟩] }

private def strike : CardInstance :=
  { instanceId := 1, ownerId := 1, modelId := ModelId.mkCard "STRIKE_DEFECT", cardType := .attack
    rarity := .basic, targetType := .anyEnemy, energyCost := CardEnergyCost.mkCanonical 1
    baseDamage := Dec.ofNat 6, tags := [.strike] }

private def defend : CardInstance :=
  { instanceId := 2, ownerId := 1, modelId := ModelId.mkCard "DEFEND_DEFECT", cardType := .skill
    rarity := .basic, targetType := .self, energyCost := CardEnergyCost.mkCanonical 1
    baseBlock := Dec.ofNat 5, gainsBlock := true }

private def initial : Expedition :=
  { currentHp := 53, maxHp := 75, actCount := 2
    nav :=
      { actMap := map1, currentCoord := start
        unknownOdds := { monsterOdds := Dec.ofScaled 50 2 }
        runState := { players := [
          { playerId := 1, creatureId := 101, characterId := ModelId.mkCharacter "DEFECT"
            baseOrbSlots := 3, deck := [strike, defend] }] } } }

private def target (hp : Nat) (model : String := "CULTIST") : Creature :=
  { id := 200, side := .enemy, modelId := ModelId.mkMonster model, currentHp := hp, maxHp := hp }

private def encounter (rewards : List ExpeditionReward := []) : ExpeditionEncounter :=
  { id := ⟨"ENCOUNTER", "EXPEDITION_EXAMPLE"⟩, enemies := [target 6], rewards := rewards }

private def go (s : Expedition) (a : ExpeditionAction) : Except String Expedition :=
  s.step fullVanillaEffectEnv a

private def check (test : Bool) (name : String) : Except String Unit :=
  unless test do throw name

private def rejects (s : Expedition) (a : ExpeditionAction) : Bool :=
  match go s a with
  | .error _ => true
  | .ok _ => false

private def play (s : Expedition) (card : CardInstance) (target : Option CreatureId := none) : Except String Expedition := do
  let some pcs := s.combat.bind (·.findPlayer 1) |>.bind (·.combatState) | throw "no combat hand"
  let some c := pcs.piles.hand.find? (·.modelId == card.modelId) | throw s!"missing {card.modelId.entry}"
  go s (.combatInput (.playCard c.instanceId target))

private def atFirstPoint : Except String Expedition := go initial (.enterPoint start .event)

private def advanceToA : Except String Expedition := do
  let s ← atFirstPoint
  let s ← go s .leaveRoom
  go s (.enterPoint roomA .monster)

private def win (s : Expedition) : Except String Expedition := do
  let s ← go s (.startEncounter (encounter []))
  let s ← play s strike (some 200)
  go s .leaveRewards

private def capacitor : CardInstance :=
  { instanceId := 0, ownerId := 1, modelId := ModelId.mkCard "CAPACITOR", cardType := .power
    rarity := .uncommon, targetType := .self, energyCost := CardEnergyCost.mkCanonical 1 }

private def csv (xs : List Nat) : String := String.intercalate "," (xs.map toString)
private def bit (b : Bool) : Nat := if b then 1 else 0

/-- Two ordinary fights and separate Boss, act and final-event transitions. -/
private def expeditionRoute : Except String (List String) := do
  let aRoom ← advanceToA
  let a ← go aRoom (.startEncounter (encounter [.independent (.gold 12), .independent (.cards [strike, capacitor])]))
  let a ← play a defend
  let aBlock := (a.combat.bind (·.findCreature 101)).map (·.block) |>.getD 0
  check (aBlock == 5) "block in A"
  let a ← play a strike (some 200)
  check (a.phase == .rewards && a.combat.isNone && a.currentHp == 53 && a.maxHp == 75) "won A"
  let pendingRejected := rejects a .leaveRewards
  let invalidChoiceRejected := rejects a (.chooseCard 1 2)
  check (pendingRejected && invalidChoiceRejected) "unresolved and invalid card index"
  let a ← go a (.claimGold 0)
  let duplicateGold := rejects a (.claimGold 0)
  check (a.nav.runState.gold == 111 && duplicateGold) "gold only once"
  let a ← go a (.chooseCard 1 1)
  let duplicateCard := rejects a (.chooseCard 1 0)
  check duplicateCard "card only once"
  let aEvidence := csv [initial.nav.runState.gold, aBlock, a.nav.runState.gold, bit invalidChoiceRejected,
    bit duplicateGold, bit duplicateCard, bit pendingRejected]
  let a ← go a .leaveRewards
  let danglingRejected := rejects a (.enterPoint dangling .monster)
  let absentRejected := rejects a (.enterPoint boss .boss)
  check (danglingRejected && absentRejected) "dangling and absent edges"
  let b ← go a (.enterPoint roomB .monster)
  let b ← go b (.startEncounter (encounter [.independent (.cards [strike])]))
  let some player := b.combat.bind (·.findPlayer 1) | throw "no B player"
  let some pcs := player.combatState | throw "no B combat state"
  let decks := player.deck.map (·.modelId)
  let fresh := pcs.piles.draw.isEmpty && pcs.piles.discard.isEmpty && pcs.piles.exhaust.isEmpty && pcs.piles.play.isEmpty &&
    pcs.piles.hand.all (fun c => c.energyCost.localModifiers.isEmpty && !player.deck.any (·.instanceId == c.instanceId))
  let bBlock := (b.combat.bind (·.findCreature 101)).map (·.block) |>.getD 999
  check (decks == [strike.modelId, defend.modelId, capacitor.modelId] &&
    pcs.piles.hand.length == 3 && fresh && bBlock == 0 && b.currentHp == 53 && b.maxHp == 75 &&
    pcs.orbQueue.capacity == 3 && pcs.energy == 3 && b.nav.runState.gold == 111) "fresh B combat"
  let combatHp := (b.combat.bind (·.findCreature 101)).map (·.currentHp) |>.getD 0
  check (combatHp == b.currentHp) "combat HP carries across rooms"
  let bHp := b.currentHp
  let bMax := b.maxHp
  let b ← play b capacitor
  let some charged := b.combat.bind (·.findPlayer 1) |>.bind (·.combatState) | throw "missing charged player"
  check (charged.orbQueue.capacity == 5) "CAPACITOR in B"
  let b ← play b strike (some 200)
  let b ← go b (.skipReward 0)
  let skipRejected := rejects b (.chooseCard 0 0)
  let afterSkip := b.nav.runState.players.head?.map (·.deck.length) |>.getD 0
  check (skipRejected && afterSkip == 3) "B skip"
  let bEvidence := csv [bHp, bMax, bBlock, pcs.energy, pcs.piles.hand.length, pcs.orbQueue.capacity,
    charged.orbQueue.capacity, decks.length, (decks.filter (· == capacitor.modelId)).length, bit fresh,
    bit skipRejected, afterSkip]
  let b ← go b .leaveRewards
  let c ← go b (.enterPoint boss .boss)
  let c ← win c
  let firstBossMap := c.phase == .map && rejects c (.enterNextAct map2)
  check firstBossMap "first Boss does not skip second"
  let c ← go c (.enterPoint secondBoss .boss)
  let c ← win c
  let act1Floors := c.nav.runState.totalFloors
  check (c.phase == .nextAct && act1Floors == 5) "second Boss completes act"
  let c ← go c (.enterNextAct map2)
  let actReset := c.nav.visited.isEmpty && c.nav.currentCoord == map2.startPoint &&
    c.nav.runState.totalFloors == act1Floors && c.nav.unknownOdds.monsterOdds == c.nav.unknownOdds.baseMonsterOdds
  check actReset "reset act navigation"
  let c ← go c (.enterPoint start .event)
  let c ← go c .leaveRoom
  let c ← go c (.enterPoint boss .boss)
  let c ← win c
  let earlyVictoryRejected := c.phase == .nextAct && rejects c .confirmVictory
  check earlyVictoryRejected "cannot win from rewards or Boss"
  let c ← go c .enterFinalEvent
  let reachedEvent := c.phase == .finalEvent
  check (reachedEvent && c.nav.runState.totalFloors == 7) "final event adds no map floor"
  let c ← go c .confirmVictory
  let victory := c.phase == .terminal .victory
  let closed := rejects c .abandon
  check (victory && closed) "terminal is closed"
  pure [aEvidence, bEvidence, csv [bit danglingRejected, bit absentRejected, bit firstBossMap,
    act1Floors, bit actReset, bit earlyVictoryRejected, bit reachedEvent, c.nav.runState.totalFloors,
    bit victory, bit closed]]

private def expeditionBoundaryCases : Except String (List String) := do
  let event ← atFirstPoint
  let wrongPhase := rejects event (.enterPoint roomA .monster)
  check wrongPhase "must finish room before moving"
  let child ← go event (.enterSubroom .monster)
  let child ← go child (.restoreRewards [.linked [.gold 2, .cards [defend]]] true)
  let restoreFloor := child.nav.runState.totalFloors
  let noRestart := child.combat.isNone && rejects child (.startEncounter (encounter []))
  check (restoreFloor == 1 && noRestart) "restore combat reward boundary without another floor or battle"
  let child ← go child (.claimGold 0)
  let linkedGold := child.nav.runState.gold
  let linkedClosed := rejects child (.chooseCard 0 0 1)
  check (linkedClosed && linkedGold == 101) "linked alternative is closed"
  let parent ← go child .leaveRewards
  let parentResumed := parent.phase == .room && parent.nav.runState.currentRoom == .event && parent.nav.visited == [start]
  check parentResumed "resume parent"
  let a ← advanceToA
  let lethalEnemy := { target 80 "COOP_GUARDIAN" with monster := some { modelId := ModelId.mkMonster "COOP_GUARDIAN" } }
  let a ← go { a with currentHp := 1 } (.startEncounter { encounter [.independent (.gold 12)] with enemies := [lethalEnemy] })
  let lost ← go a (.combatInput .endTurn)
  let defeat := lost.phase == .terminal .defeat && rejects lost (.claimGold 0)
  check (defeat && lost.currentHp == 0 && lost.rewards.isEmpty && lost.nav.runState.gold == 99)
    "defeat does not offer rewards"
  pure [csv [bit wrongPhase, restoreFloor, bit noRestart, linkedGold, bit linkedClosed, bit parentResumed],
    csv [lost.currentHp, lost.nav.runState.gold, lost.rewards.length, bit defeat]]

def expeditionReferenceProjection : String :=
  match expeditionRoute, expeditionBoundaryCases with
  | .ok route, .ok boundaries => String.intercalate "|" (route ++ boundaries)
  | .error e, _ | _, .error e => s!"EXPEDITION_ERROR: {e}"

private def expeditionCombatPersistence : Except String Unit := do
  let modded : CardInstance :=
    { instanceId := 3, ownerId := 1, modelId := ModelId.mkCard "MODDED", cardType := .skill
      rarity := .rare, targetType := .self, energyCost := CardEnergyCost.mkCanonical 0 }
  let room ← advanceToA
  let some p := room.nav.runState.players.head? | throw "missing deck"
  let p := { p with
    deck := p.deck ++ [modded, { modded with instanceId := 4 }]
    potions := [some { modelId := ModelId.mkPotion "BLOCK_POTION" }] }
  let a ← go { room with nav.runState.players := [p] }
    (.startEncounter { encounter [] with enemies := [target 6 "SEAPUNK"] })
  let a ← go a (.combatInput .endTurn)
  let a ← go a (.combatInput (.usePotion 0))
  let a ← play a modded
  let some aP := a.combat.bind (·.findPlayer 1) | throw "missing A combat player"
  let some aPcs := aP.combatState | throw "missing A combat state"
  let cost (c : CardInstance) := c.energyCost.getWithModifiers c.isCanonical
  check ((aPcs.piles.hand.find? (·.modelId == modded.modelId)).map cost == some 0 &&
    (aPcs.piles.discard.find? (·.modelId == modded.modelId)).map cost == some 1 &&
    aPcs.orbQueue.capacity == 4 && (aP.deck.filter (·.modelId == modded.modelId)).all (fun c => cost c == 0))
    "MODDED updates only the played instance"
  let a ← play a strike (some 200)
  let some after := a.nav.runState.players.head? | throw "missing committed player"
  check (a.currentHp == 42 && after.potions == [none] && after.deck == p.deck &&
    after.combatState.isNone && a.combat.isNone) "victory commits HP and used potion, not combat cards"
  let a ← go a .leaveRewards
  let b ← go a (.enterPoint roomB .monster)
  let b ← go b (.startEncounter (encounter []))
  let some bc := b.combat | throw "missing next combat"
  let some bcPlayer := bc.findPlayer 1 | throw "missing next combat player"
  let some bPcs := bcPlayer.combatState | throw "missing next combat piles"
  let twins := bPcs.piles.hand.filter (·.modelId == modded.modelId)
  check ((bc.findCreature 101).map (·.currentHp) == some 42 && bcPlayer.potions == [none] &&
    twins.length == 2 && twins.all (fun c => cost c == 0) && bPcs.orbQueue.capacity == 3 &&
    bc.shuffleRng == some (a.nav.runState.rngSet.shuffle.nextULong).2)
    "fresh fight resets both costs and orb capacity, advances run shuffle, and carries health/items"

private def passed (result : Except String α) : Bool :=
  match result with
  | .ok _ => true
  | .error _ => false

def allExpeditionTests : List (String × Bool) :=
  [("expedition_cross_room_act_and_final_event", passed expeditionRoute),
   ("expedition_restore_linked_subroom_and_defeat", passed expeditionBoundaryCases),
   ("expedition_persists_hp_items_not_combat_costs", passed expeditionCombatPersistence)]

end Sts2Model.Examples
