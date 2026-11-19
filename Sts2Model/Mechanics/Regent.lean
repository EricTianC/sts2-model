/-
  Regent mechanics: Stars resource, `ForgeCmd.Forge` & `SovereignBlade` damage scaling,
  and excess energy payment with Stars (1 missing energy = 2 stars).
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Commands/ForgeCmd.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models.Cards/SovereignBlade.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.Players/PlayerCombatState.cs`
-/
import Sts2Model.Command.CardCmd

namespace Sts2Model.Mechanics

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook
open Sts2Model.Command

def sovereignBladeModelId : ModelId := ModelId.mkCard "SOVEREIGN_BLADE"

/-- Canonical unupgraded `SovereignBlade` instance (`cost = 2`, `Attack`, `Token`, `baseDamage = 10`).
    Ref: `SovereignBlade.cs` line 23 & 118. -/
def mkSovereignBlade (instanceId : CardInstanceId) (ownerId : PlayerId)
    (damage : Dec := Dec.ofInt 10) : CardInstance :=
  { instanceId := instanceId
  , modelId := sovereignBladeModelId
  , ownerId := ownerId
  , cardType := .attack
  , rarity := .token
  , targetType := .anyEnemy
  , energyCost := CardEnergyCost.mkCanonical 2
  , baseDamage := damage }

/-- Return all non-dupe `SovereignBlade` cards in a player's combat piles (`includeExhausted` flag
    matches `ForgeCmd.GetSovereignBlades`, `ForgeCmd.cs` line 67). -/
def getSovereignBlades (pcs : PlayerCombatState) (includeExhausted : Bool) : List CardInstance :=
  let cards :=
    if includeExhausted then
      pcs.piles.hand ++ pcs.piles.draw ++ pcs.piles.discard ++ pcs.piles.play ++ pcs.piles.exhaust
    else
      pcs.piles.hand ++ pcs.piles.draw ++ pcs.piles.discard ++ pcs.piles.play
  cards.filter fun c => !c.isDupe && c.modelId == sovereignBladeModelId

def mapPileCards (piles : PlayerPiles) (f : CardInstance → CardInstance) : PlayerPiles :=
  { hand := piles.hand.map f
  , draw := piles.draw.map f
  , discard := piles.discard.map f
  , exhaust := piles.exhaust.map f
  , play := piles.play.map f }

/-- `ForgeCmd.Forge`: generates a `SovereignBlade` into hand if no non-exhausted blade exists,
    then increases damage of ALL non-dupe `SovereignBlade` cards across all piles by `amount`. -/
def forgeSovereignBlade (cs : CombatState) (pid : PlayerId) (amount : Dec) : CombatState :=
  if cs.isEnding then cs
  else match cs.findPlayer pid with
    | none => cs
    | some player =>
        match player.combatState with
        | none => cs
        | some pcs =>
            let hasActiveBlade := !(getSovereignBlades pcs false).isEmpty
            let (cs1, pcs1) :=
              if hasActiveBlade then (cs, pcs)
              else
                let (newCid, csAlloc) := cs.allocInstanceId
                let blade := mkSovereignBlade newCid pid (Dec.add (Dec.ofInt 10) pcs.sovereignBladeBonus)
                let (piles', _) :=
                  if pcs.piles.hand.length ≥ PlayerPiles.maxCardsInHand then
                    ({ pcs.piles with discard := pcs.piles.discard ++ [blade] }, true)
                  else
                    ({ pcs.piles with hand := pcs.piles.hand ++ [blade] }, true)
                let st' := { pcs with piles := piles', sovereignBladeForged := true }
                (csAlloc.updatePlayer pid (fun p => { p with combatState := some st' }), st')
            let pilesUpdated := mapPileCards pcs1.piles fun c =>
              if !c.isDupe && c.modelId == sovereignBladeModelId then
                { c with baseDamage := Dec.add c.baseDamage amount }
              else c
            let stFinal :=
              { pcs1 with
                piles := pilesUpdated
              , sovereignBladeBonus := Dec.add pcs1.sovereignBladeBonus amount }
            cs1.updatePlayer pid (fun p => { p with combatState := some stFinal })

def gainStars (cs : CombatState) (pid : PlayerId) (amount : Nat) : CombatState :=
  let cs1 := cs.updatePlayer pid fun p =>
    match p.combatState with
    | none => p
    | some pcs => { p with combatState := some (pcs.gainStars amount) }
  cs1.recordHistory (.starsModified cs1.roundNumber pid (amount : Int))

def loseStars (cs : CombatState) (pid : PlayerId) (amount : Nat) : CombatState × Nat :=
  match cs.findPlayer pid |>.bind (·.combatState) with
  | none => (cs, 0)
  | some pcs =>
      let spent := min pcs.stars amount
      let cs1 := cs.updatePlayer pid fun p =>
        match p.combatState with
        | none => p
        | some st => { p with combatState := some (st.loseStars amount) }
      (cs1.recordHistory (.starsModified cs1.roundNumber pid (-(spent : Int))), spent)

end Sts2Model.Mechanics
