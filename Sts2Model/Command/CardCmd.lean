/-
  Card pile movement, drawing, shuffling, resource spending, CanPlay validation,
  deck-to-combat cloning, and card play resolution.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Commands/CardCmd.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Commands/CardPileCmd.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models/CardModel.cs` (`CanPlay`, `SpendResources`, `OnPlayWrapper`)
-/
import Sts2Model.Core.Rng
import Sts2Model.Model.State
import Sts2Model.Hook.Pipeline

namespace Sts2Model.Command

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook

/-- Remove card by `instanceId` from a list, returning `(removed?, remaining)`. -/
def removeCardById (cid : CardInstanceId) : List CardInstance → Option CardInstance × List CardInstance
  | [] => (none, [])
  | c :: cs =>
      if c.instanceId == cid then
        (some c, cs)
      else
        let (found, rest) := removeCardById cid cs
        (found, c :: rest)

/-- Insert a card into a pile list at `pos`. Ref: `CardPile.AddInternal`. -/
def insertIntoPileList (pos : CardPilePosition) (c : CardInstance) (xs : List CardInstance) :
    List CardInstance :=
  match pos with
  | .top => c :: xs
  | _    => xs ++ [c]

/-- Atomically move a card from whichever combat pile currently holds it into `destPile`.
    Preserves total card count and pile disjointness.
    Ref: `CardPileCmd.Add` + `CardModel.RemoveFromCurrentPile`. -/
def moveCard (piles : PlayerPiles) (cid : CardInstanceId) (destPile : PileType)
    (pos : CardPilePosition := .bottom) (transformCard : CardInstance → CardInstance := id) :
    PlayerPiles × Option CardInstance :=
  match piles.findPileOf cid with
  | none => (piles, none)
  | some srcPile =>
      let (optCard, srcRest) := removeCardById cid (piles.getPile srcPile)
      match optCard with
      | none => (piles, none)
      | some card =>
          let piles1 := piles.setPile srcPile srcRest
          let card' := transformCard card
          if destPile == .none || destPile == .deck then
            (piles1, some card')
          else
            let dstList := insertIntoPileList pos card' (piles1.getPile destPile)
            (piles1.setPile destPile dstList, some card')

/-- Remove a card from all combat piles (used for Power cards and dupes after play).
    Ref: `CardPileCmd.RemoveFromCombat`. -/
def removeCardFromCombat (piles : PlayerPiles) (cid : CardInstanceId) : PlayerPiles × Option CardInstance :=
  moveCard piles cid .none

/-- Shuffle discard pile into draw pile using `Rng.unstableShuffle`.
    Ref: `CardPileCmd.Shuffle`. -/
def shuffleDiscardIntoDraw (piles : PlayerPiles) (rng : Rng) : PlayerPiles × Rng :=
  let (shuffled, rng') := Rng.unstableShuffle (piles.draw ++ piles.discard) rng
  ({ piles with draw := shuffled, discard := [] }, rng')

/-- Draw up to `count` cards respecting hand limit (`maxCardsInHand = 10`),
    auto-shuffling discard into draw when draw is empty, and checking `Hook.ShouldDraw`.
    Ref: `CardPileCmd.Draw`. -/
def drawCards (cs : CombatState) (reg : BehaviorRegistry) (pid : PlayerId)
    (count : Nat) (fromHandDraw : Bool := false)
    (modSubscribers : List (ModId × ModelId) := []) :
    CombatState × List CardInstance :=
  let rec loop (fuel : Nat) (state : CombatState) (drawn : List CardInstance) :
      CombatState × List CardInstance :=
    match fuel with
    | 0 => (state, drawn)
    | n + 1 =>
        match state.findPlayer pid with
        | none => (state, drawn)
        | some player =>
            match player.combatState with
            | none => (state, drawn)
            | some pcs =>
                if pcs.piles.hand.length ≥ PlayerPiles.maxCardsInHand then
                  (state, drawn)
                else if !(shouldDraw state reg player fromHandDraw modSubscribers).1 then
                  (state, drawn)
                else
                  let (pilesAfterShuffle, rng') :=
                    if pcs.piles.draw.isEmpty && !pcs.piles.discard.isEmpty then
                      shuffleDiscardIntoDraw pcs.piles state.rng
                    else
                      (pcs.piles, state.rng)
                  match pilesAfterShuffle.draw with
                  | [] =>
                      let pcs' := { pcs with piles := pilesAfterShuffle }
                      (state.updatePlayer pid (fun p => { p with combatState := some pcs' }), drawn)
                  | topCard :: restDraw =>
                      let piles' := { pilesAfterShuffle with
                        draw := restDraw
                        hand := pilesAfterShuffle.hand ++ [topCard] }
                      let pcs' := { pcs with piles := piles' }
                      let state' := { state.updatePlayer pid (fun p => { p with combatState := some pcs' }) with rng := rng' }
                      loop n state' (drawn ++ [topCard])
  loop count cs []

/-- Discard a card from hand (or another combat pile) into discard pile.
    Ref: `CardCmd.Discard`. -/
def discardCard (cs : CombatState) (pid : PlayerId) (cid : CardInstanceId) : CombatState :=
  cs.updatePlayer pid fun p =>
    match p.combatState with
    | none => p
    | some pcs =>
        let (piles', _) := moveCard pcs.piles cid .discard .bottom
        { p with combatState := some { pcs with piles := piles' } }

/-- Exhaust a card into the exhaust pile (unless `CardKeyword.eternal` prevents removal?
    Note: `Eternal` cards cannot be removed/exhausted by some effects; here standard `Exhaust` moves to ExhaustPile).
    Ref: `CardCmd.Exhaust`. -/
def exhaustCard (cs : CombatState) (pid : PlayerId) (cid : CardInstanceId) : CombatState :=
  cs.updatePlayer pid fun p =>
    match p.combatState with
    | none => p
    | some pcs =>
        let (piles', _) := moveCard pcs.piles cid .exhaust .bottom
        { p with combatState := some { pcs with piles := piles' } }

/-- Target validity matching `CardModel.IsValidTarget`. -/
def isValidCardTarget (cs : CombatState) (owner : Player) (card : CardInstance)
    (targetId : Option CreatureId) : Bool :=
  let ownerSide := (cs.findCreature owner.creatureId).map (·.side) |>.getD .player
  match targetId with
  | none => card.targetType != .anyEnemy && card.targetType != .anyAlly
  | some tid =>
      match cs.findCreature tid with
      | none => false
      | some t =>
          if !t.isAlive then false
          else match card.targetType with
            | .anyEnemy => t.side != ownerSide
            | .anyAlly  => t.side == ownerSide
            | _         => false

/-- Evaluate effective energy cost of `card` including local & global combat hooks. -/
def effectiveEnergyCost (cs : CombatState) (reg : BehaviorRegistry) (card : CardInstance)
    (modSubscribers : List (ModId × ModelId) := []) : Int :=
  card.energyCost.getWithModifiers card.isCanonical CostModifiers.all fun localAmt =>
    (modifyEnergyCostInCombat cs reg card (Dec.ofInt localAmt) modSubscribers).truncate

/-- Evaluate effective star cost of `card`. Ref: `CardModel.GetStarCostWithModifiers`. -/
def effectiveStarCost (pcs : PlayerCombatState) (card : CardInstance) : Int :=
  if card.hasStarCostX then (pcs.stars : Int)
  else match card.temporaryStarCost with
    | some tc => (tc.cost : Int)
    | none    => card.baseStarCost

/-- Full `CardModel.CanPlay` check. Ref: `CardModel.cs` lines 1887-1917. -/
def canPlay (cs : CombatState) (reg : BehaviorRegistry) (pid : PlayerId)
    (card : CardInstance) (autoPlay : AutoPlayType := .none)
    (modSubscribers : List (ModId × ModelId) := []) : Bool × UnplayableReason :=
  match cs.findPlayer pid with
  | none => (false, UnplayableReason.none)
  | some player =>
      match player.combatState with
      | none => (false, UnplayableReason.none)
      | some pcs =>
          let unplayableKw := card.hasKeyword .unplayable ||
            (match card.affliction with | some a => a.preventsPlay | none => false)
          let eCost : Int :=
            if card.energyCost.costsX then (pcs.energy : Int)
            else effectiveEnergyCost cs reg card modSubscribers
          let sCost : Int := effectiveStarCost pcs card
          let excessWithStars := shouldPayExcessEnergyCostWithStars cs reg player modSubscribers
          let (_, _, resReason) := pcs.checkResourcesFor eCost sCost excessWithStars
          let noLivingAllies :=
            card.targetType == .anyAlly && (cs.allies.filter Creature.isAlive).length ≤ 1
          let blockedByHook := !(shouldPlay cs reg card autoPlay modSubscribers).1
          let reason : UnplayableReason :=
            { hasUnplayableKeyword := unplayableKw
            , blockedByHook := blockedByHook
            , blockedByCardLogic := false
            , energyCostTooHigh := resReason.energyCostTooHigh
            , starCostTooHigh := resReason.starCostTooHigh
            , noLivingAllies := noLivingAllies }
          (reason.isPlayable, reason)

/-- Spend energy & stars for `card`, returning `(updatedCombatState, energySpent, starsSpent)`.
    Guaranteed never to underflow when `canPlay` held. Ref: `CardModel.SpendResources`. -/
def spendResources (cs : CombatState) (reg : BehaviorRegistry) (pid : PlayerId)
    (card : CardInstance) (modSubscribers : List (ModId × ModelId) := []) :
    CombatState × Nat × Nat :=
  match cs.findPlayer pid with
  | none => (cs, 0, 0)
  | some player =>
      match player.combatState with
      | none => (cs, 0, 0)
      | some pcs =>
          let eCost : Int :=
            if card.energyCost.costsX then (pcs.energy : Int)
            else effectiveEnergyCost cs reg card modSubscribers
          let sCost : Int := effectiveStarCost pcs card
          let excessWithStars := shouldPayExcessEnergyCostWithStars cs reg player modSubscribers
          let (eReq, sReq, _) := pcs.checkResourcesFor eCost sCost excessWithStars
          let eSpent := min pcs.energy eReq
          let sSpent := min pcs.stars sReq
          let pcs' := (pcs.loseEnergy eSpent).loseStars sSpent
          let cs1 := cs.updatePlayer pid (fun p => { p with combatState := some pcs' })
          let cs2 := if eSpent > 0 then cs1.recordHistory (.energySpent cs1.roundNumber pid eSpent) else cs1
          let cs3 := if sSpent > 0 then cs2.recordHistory (.starsModified cs2.roundNumber pid (-(sSpent : Int))) else cs2
          (cs3, eSpent, sSpent)

/-- Clone out-of-combat `player.deck` into fresh mutable combat cards in `draw` pile.
    Note: `player.deck` itself is never mutated during combat.
    Ref: `PileType.Deck` docstring & `CombatManager.SetUpCombat`. -/
def cloneDeckForCombat (player : Player) (baseInstanceId : Nat := 10000) : PlayerPiles × Nat :=
  let (cards, nextId) := player.deck.foldl (fun (acc, idCounter) dc =>
    let cloned : CardInstance := { dc with instanceId := idCounter, isCanonical := false }
    (acc ++ [cloned], idCounter + 1)) ([], baseInstanceId)
  ({ draw := cards }, nextId)

/-- Execute full card play transition (`Hand -> Play -> AfterPlayCleanup -> ResultPile`).
    Ref: `CardModel.OnPlayWrapper`. -/
def playCard (cs : CombatState) (reg : BehaviorRegistry) (pid : PlayerId)
    (cid : CardInstanceId) (targetId : Option CreatureId := none)
    (effectFn : CombatState → CardPlay → CombatState := fun s _ => s)
    (modSubscribers : List (ModId × ModelId) := []) :
    CombatState × Bool :=
  match cs.findPlayer pid with
  | none => (cs, false)
  | some player =>
      match player.combatState with
      | none => (cs, false)
      | some pcs =>
          match pcs.piles.findCard cid with
          | none => (cs, false)
          | some card =>
              let (ok, _) := canPlay cs reg pid card .none modSubscribers
              if !ok then (cs, false)
              else
                let (csSpent, eSpent, sSpent) := spendResources cs reg pid card modSubscribers
                -- Move Hand -> Play
                let csInPlay := csSpent.updatePlayer pid fun p =>
                  match p.combatState with
                  | none => p
                  | some pSt =>
                      let (piles', _) := moveCard pSt.piles cid .play .bottom (fun c =>
                        if c.energyCost.costsX then
                          { c with energyCost := { c.energyCost with capturedXValue := eSpent } }
                        else c)
                      { p with
                        combatState := some { pSt with
                          piles := piles'
                          playedTagsThisTurn := pSt.playedTagsThisTurn ++ card.tags } }
                let resultPile := card.defaultResultPile
                let playInfo : CardPlay :=
                  { cardId := cid
                  , playerId := pid
                  , targetId := targetId
                  , resultPile := resultPile
                  , energySpent := eSpent
                  , starsSpent := sSpent }
                let csStarted := csInPlay.recordHistory (.cardPlayStarted csInPlay.roundNumber csInPlay.currentSide playInfo card.tags)
                let csAfterEffect := effectFn csStarted playInfo
                let csFinished := csAfterEffect.recordHistory (.cardPlayFinished csAfterEffect.roundNumber csAfterEffect.currentSide playInfo card.tags)
                -- Cleanup & move Play -> resultPile
                let csFinal := csFinished.updatePlayer pid fun p =>
                  match p.combatState with
                  | none => p
                  | some pSt =>
                      let (piles', _) := moveCard pSt.piles cid resultPile .bottom CardInstance.afterCardPlayedCleanup
                      { p with combatState := some { pSt with piles := piles' } }
                (csFinal, true)

end Sts2Model.Command
