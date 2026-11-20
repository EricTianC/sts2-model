/-
  Out-of-combat Run transition loop: map traversal, `LinkedRewardSet` exclusivity,
  and act advancement with `UnknownMapPointOdds` reset + Dread dominion setup.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Rewards/LinkedRewardSet.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Runs/RunState.cs`
-/
import Sts2Model.Run.Map
import Sts2Model.Run.Odds
import Sts2Model.Mechanics.Dread

namespace Sts2Model.Run

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Mechanics

/-- A reward option inside a `LinkedRewardSet` (`LinkedRewardSet.cs`). -/
inductive RewardKind where
  | gold (amount : Nat)
  | card (modelId : ModelId)
  | relic (modelId : ModelId)
  | potion (modelId : ModelId)
  deriving Repr, DecidableEq, Inhabited

structure LinkedRewardSet (α : Type := RewardKind) where
  rewards : List α := []
  claimed : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace LinkedRewardSet

/-- Claiming one reward in a linked set claims that item and closes all linked alternatives. -/
def selectIndex (lrs : LinkedRewardSet α) (idx : Nat) : LinkedRewardSet α × Option α :=
  if lrs.claimed then (lrs, none)
  else match lrs.rewards[idx]? with
    | none   => (lrs, none)
    | some r => ({ rewards := [], claimed := true }, some r)

end LinkedRewardSet

/-- Extended run navigation wrapper bundling `RunState`, `UnknownMapPointOdds`, `RelicGrabBag`,
    and visited coordinates on the current `ActMap`. -/
structure RunNavigationState where
  runState     : RunState
  actMap       : ActMap
  currentCoord : MapCoord
  visited      : List MapCoord := []
  unknownOdds  : UnknownMapPointOdds := {}
  grabBag      : RelicGrabBag := {}
  rarityOdds   : CardRarityOddsF32 := {}
  potionOdds   : PotionRewardOdds := {}
  deriving Repr, DecidableEq

def enterMapPoint (nav : RunNavigationState) (dest : MapCoord) (room : RoomType) :
    RunNavigationState × Bool :=
  if nav.actMap.hasEdge nav.currentCoord dest then
    let rs' := { nav.runState with
      currentRoom := room
      totalFloors := nav.runState.totalFloors + 1 }
    ({ nav with
       runState := rs'
     , currentCoord := dest
     , visited := nav.visited ++ [dest] }, true)
  else
    (nav, false)

def advanceActWithDread (nav : RunNavigationState) (newMap : ActMap)
    (cfg : DreadActConfig) (nextCardId : Nat) : RunNavigationState × Nat :=
  let (rs', nextId') := dreadAfterActEntered nav.runState cfg nextCardId
  ({ nav with
     runState := rs'
   , actMap := newMap
   , currentCoord := newMap.startPoint
   , visited := [newMap.startPoint]
   , unknownOdds := nav.unknownOdds.resetToBase }, nextId')

end Sts2Model.Run
