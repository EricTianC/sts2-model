/-
  Fool mechanics: Arrow slots & shooting / impaling / dislodging / destroying (`ArrowCmd`),
  plus Melody tags (`Wah`, `Cho`, `Ki`) and identity-based first-play check (`MelodyCmd`).
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.FoolArrows/ArrowSlot.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Entities.FoolArrows/ArrowStatus.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Commands/ArrowCmd.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models.Powers/ImpaledPower.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Commands/MelodyCmd.cs`
-/
import Sts2Model.Command.PowerCmd

namespace Sts2Model.Mechanics

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook
open Sts2Model.Command

def impaledPowerModelId : ModelId := ModelId.mkPower "IMPALED_POWER"

def isMelodyTag : CardTag → Bool
  | .wah | .cho | .ki => true
  | _ => false

/-- `ArrowCmd.GainArrowSlot`. -/
def gainArrowSlot (cs : CombatState) (pid : PlayerId) (destroyAfterImpaled : Bool := false) : CombatState :=
  cs.updatePlayer pid fun p =>
    match p.combatState with
    | none => p
    | some pcs =>
        { p with combatState := some { pcs with arrows := pcs.arrows ++ [{ status := .retrieved, destroyAfterImpaled := destroyAfterImpaled }] } }

/-- Number of available arrows ready to shoot (`ArrowStatus.retrieved`). -/
def availableArrowCount (cs : CombatState) (pid : PlayerId) : Nat :=
  match cs.findPlayer pid |>.bind (·.combatState) with
  | none => 0
  | some pcs => pcs.availableArrowCount

/-- Find the last available (`retrieved`) arrow index matching `TryGetNextArrowToShoot` (`LastOrDefault`). -/
private def findLastAvailableArrowIdx (arrows : List ArrowSlot) : Option Nat :=
  (arrows.zip (List.range arrows.length)).foldl (fun best (a, idx) =>
    if a.isAvailable then some idx else best) none

/-- Shoot the last available arrow, setting its status to `ArrowStatus.away`, and apply/stack
    `ImpaledPower` on `targetId` (`hitCounter = 3`, `InstancedPerApplier`).
    Returns `(updatedState, arrowShotIdx?)`. -/
def shootArrowAtTarget (cs : CombatState) (reg : BehaviorRegistry) (pid : PlayerId) (targetId : CreatureId)
    (modSubscribers : List (ModId × ModelId) := []) : CombatState × Option Nat :=
  match cs.findPlayer pid, cs.findCreature targetId with
  | some player, some target =>
      if target.isDead then (cs, none)
      else match player.combatState with
        | none => (cs, none)
        | some pcs =>
            match findLastAvailableArrowIdx pcs.arrows with
            | none => (cs, none)
            | some idx =>
                let shotSlot := pcs.arrows[idx]!
                let arrows' := pcs.arrows.mapIdx fun i a => if i == idx then { a with status := .away } else a
                let cs1 := cs.updatePlayer pid fun p =>
                  match p.combatState with
                  | none => p
                  | some st => { p with combatState := some { st with arrows := arrows' } }
                let impaledTmpl : PowerInstance :=
                  { instanceId := 0
                  , modelId := impaledPowerModelId
                  , ownerId := targetId
                  , powerType := .none
                  , stackType := .counter
                  , instanceType := .instancedPerApplier }
                let (cs2, _) := applyPower cs1 reg impaledTmpl targetId (Dec.ofInt 1) (some player.creatureId) modSubscribers
                if shotSlot.destroyAfterImpaled then
                  let arrowsDestroyed := arrows'.mapIdx fun i a => if i == idx then { a with status := .destroyed } else a
                  let cs3 := cs2.updatePlayer pid fun p =>
                    match p.combatState with
                    | none => p
                    | some st => { p with combatState := some { st with arrows := arrowsDestroyed } }
                  (cs3, some idx)
                else
                  (cs2, some idx)
  | _, _ => (cs, none)

/-- Retrieve an arrow slot unless already `destroyed` or `retrieved` (`ArrowCmd.RetrieveArrow`). -/
def retrieveArrowSlot (slot : ArrowSlot) : Option ArrowSlot :=
  match slot.status with
  | .destroyed => none
  | .retrieved => none
  | .away =>
      if slot.destroyAfterImpaled then some { status := .destroyed, destroyAfterImpaled := true }
      else some { status := .retrieved, destroyAfterImpaled := false }

/-- Dislodge one arrow owned by `pid` from `targetId` and return it (`ArrowCmd.DislodgeArrow`). -/
def dislodgeArrow (cs : CombatState) (pid : PlayerId) (targetId : CreatureId) (slotIdx : Nat) : CombatState :=
  match cs.findPlayer pid |>.bind (·.combatState) with
  | none => cs
  | some pcs =>
      if h : slotIdx < pcs.arrows.length then
        let slot := pcs.arrows[slotIdx]
        let arrows' := match retrieveArrowSlot slot with
          | some slot' => pcs.arrows.mapIdx fun i a => if i == slotIdx then slot' else a
          | none       => pcs.arrows
        let cs1 := cs.updatePlayer pid fun p =>
          match p.combatState with
          | none => p
          | some st => { p with combatState := some { st with arrows := arrows' } }
        -- Decrement player's ImpaledPower on target by 1 (removes at 0)
        match cs1.findPlayer pid, cs1.findCreature targetId with
        | some player, some target =>
            match target.powers.find? (fun p => p.modelId == impaledPowerModelId && p.applierId == some player.creatureId) with
            | some imp => decrementPowerById cs1 targetId imp.instanceId
            | none     => cs1
        | _, _ => cs1
      else cs

/-- Whether `player` finished playing a card with `tag` in `cs.roundNumber` (`MelodyCmd.PlayedThisTurn`). -/
def playedTagThisTurn (cs : CombatState) (pid : PlayerId) (tag : CardTag) : Bool :=
  cs.history.any fun e =>
    match e with
    | .cardPlayFinished r _ play tags => r == cs.roundNumber && play.playerId == pid && tags.contains tag
    | _ => false

/-- Distinct melody count played this turn among `{Wah, Cho, Ki}` (`MelodyCmd.MelodiesThisTurn` ∈ [0, 3]). -/
def melodiesThisTurn (cs : CombatState) (pid : PlayerId) : Nat :=
  (if playedTagThisTurn cs pid .wah then 1 else 0) +
  (if playedTagThisTurn cs pid .cho then 1 else 0) +
  (if playedTagThisTurn cs pid .ki  then 1 else 0)

/-- Number of melody cards played this turn (counts each card once even if multiple tags; `MelodyCmd.MelodyCardsPlayedThisTurn`). -/
def melodyCardsPlayedThisTurn (cs : CombatState) (pid : PlayerId) : Nat :=
  (cs.history.filter fun e =>
    match e with
    | .cardPlayFinished r _ play tags =>
        r == cs.roundNumber && play.playerId == pid && (tags.contains .wah || tags.contains .cho || tags.contains .ki)
    | _ => false).length

/-- Identity check for first play of `tag` this turn (`MelodyCmd.IsFirstPlayThisTurn`):
    compares `CardPlaysStarted` first entry with `cardPlay` rather than counting! -/
def isFirstMelodyPlayThisTurn (cs : CombatState) (play : CardPlay) (tag : CardTag) : Bool :=
  match cs.history.find? (fun e =>
    match e with
    | .cardPlayStarted r _ p tags => r == cs.roundNumber && p.playerId == play.playerId && tags.contains tag
    | _ => false) with
  | some (.cardPlayStarted _ _ p _) => p == play
  | _ => false

end Sts2Model.Mechanics
