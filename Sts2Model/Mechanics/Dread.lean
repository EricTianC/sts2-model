/-
  Dread mode lifecycle: `DreadRunModel` adding `Ascender's Bane` on `actIndex > 0`
  and attaching/removing act `DominionModel` upon entering boss encounters.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Models.Dread/DreadRunModel.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models.Dread/DominionModel.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Models.Cards/AscendersBane.cs`
-/
import Sts2Model.Model.State

namespace Sts2Model.Mechanics

open Sts2Model.Core
open Sts2Model.Model

def ascendersBaneModelId : ModelId := ModelId.mkCard "ASCENDERS_BANE"

/-- Canonical `Ascender's Bane` curse added in Dread runs after Act 0 (`AscendersBane.cs`). -/
def mkAscendersBane (instanceId : CardInstanceId) (ownerId : PlayerId) : CardInstance :=
  { instanceId := instanceId
  , modelId := ascendersBaneModelId
  , ownerId := ownerId
  , cardType := .curse
  , rarity := .curse
  , targetType := .none
  , keywords := [.eternal, .unplayable, .ethereal]
  , energyCost := CardEnergyCost.mkCanonical (-1) }

/-- Boss-paired dominion configuration for an Act in Dread mode (`DreadRunModel.ApplyCurrentDominion`). -/
structure DreadActConfig where
  actIndex            : Nat
  bossEncounterId     : ModelId
  secondBossEncounterId : Option ModelId := none
  dominionId          : ModelId
  deriving Repr, DecidableEq, Inhabited

/-- Transition run state on entering an Act in Dread mode:
    adds `Ascender's Bane` to each player's deck if `actIndex > 0`, and attaches act `dominionId`. -/
def dreadAfterActEntered (rs : RunState) (cfg : DreadActConfig) (nextCardId : Nat) : RunState × Nat :=
  let (players', nextId') :=
    if cfg.actIndex == 0 then
      (rs.players, nextCardId)
    else
      rs.players.foldl (fun (accPlayers, cid) p =>
        let curse := mkAscendersBane cid p.playerId
        (accPlayers ++ [{ p with deck := p.deck ++ [curse] }], cid + 1)) ([], nextCardId)
  ({ rs with
     currentActIndex := cfg.actIndex
   , players := players'
   , dominion := some cfg.dominionId }, nextId')

/-- `DreadRunModel.RemoveDominionIfRoomIsBoss` & `BeforeRoomEntered`:
    clears dominion from both `RunState` and `CombatState` when entering the act's boss encounter;
    otherwise ensures dominion is propagated into `CombatState`. -/
def dreadBeforeRoomEntered (rs : RunState) (cs : CombatState) (roomType : RoomType)
    (encounterId : ModelId) (cfg : DreadActConfig) : RunState × CombatState :=
  let isBoss :=
    roomType == .boss &&
    (encounterId == cfg.bossEncounterId || some encounterId == cfg.secondBossEncounterId)
  if isBoss then
    ({ rs with dominion := none }, { cs with dominion := none })
  else
    let dom := rs.dominion.orElse (fun _ => some cfg.dominionId)
    ({ rs with dominion := dom }, { cs with dominion := dom })

end Sts2Model.Mechanics
