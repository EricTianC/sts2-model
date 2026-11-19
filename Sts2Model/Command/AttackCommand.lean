/-
  Multi-hit AttackCommand builder modeling `Core.Commands.Builders/AttackCommand.cs`.
  Reference: `reference/sts2/MegaCrit.Sts2.Core.Commands.Builders/AttackCommand.cs`
-/
import Sts2Model.Core.Dec
import Sts2Model.Core.Enums
import Sts2Model.Model.State
import Sts2Model.Command.CreatureCmd

namespace Sts2Model.Command

open Sts2Model.Core
open Sts2Model.Model
open Sts2Model.Hook

/-- Fluent attack command builder. Ref: `Core.Commands.Builders/AttackCommand.cs`. -/
structure AttackCommand where
  damagePerHit : Dec
  hitCount     : Nat := 1
  props        : ValueProp := DamageProps.card
  dealerId     : Option CreatureId := none
  cardSource   : Option CardInstance := none
  targetIds    : List CreatureId := []
  deriving Repr, DecidableEq

namespace AttackCommand

def attack (damagePerHit : Dec) : AttackCommand :=
  { damagePerHit := damagePerHit }

def fromCard (cmd : AttackCommand) (card : CardInstance) (dealerCid : CreatureId) : AttackCommand :=
  { cmd with cardSource := some card, dealerId := some dealerCid, props := DamageProps.card }

def fromMonster (cmd : AttackCommand) (dealerCid : CreatureId) : AttackCommand :=
  { cmd with dealerId := some dealerCid, props := DamageProps.monsterMove }

def withHitCount (cmd : AttackCommand) (n : Nat) : AttackCommand :=
  { cmd with hitCount := n }

def targeting (cmd : AttackCommand) (tids : List CreatureId) : AttackCommand :=
  { cmd with targetIds := tids }

/-- Execute `hitCount` successive strikes across `targetIds`. -/
def execute (cmd : AttackCommand) (cs : CombatState) (reg : BehaviorRegistry)
    (modSubscribers : List (ModId × ModelId) := []) :
    CombatState × List DamageResult :=
  let rec loop (n : Nat) (state : CombatState) (results : List DamageResult) :
      CombatState × List DamageResult :=
    match n with
    | 0 => (state, results)
    | k + 1 =>
        let (state', rs) :=
          damage state reg cmd.targetIds cmd.damagePerHit cmd.props cmd.dealerId cmd.cardSource .all modSubscribers
        loop k state' (results ++ rs)
  loop cmd.hitCount cs []

end AttackCommand
end Sts2Model.Command
