-- Root module for the Slay the Spire 2 formal logic model.
-- Reference: reference/sts2/

import Sts2Model.Core.Dec
import Sts2Model.Core.Ids
import Sts2Model.Core.Enums
import Sts2Model.Core.Rng

import Sts2Model.Model.Cost
import Sts2Model.Model.Card
import Sts2Model.Model.Power
import Sts2Model.Model.Creature
import Sts2Model.Model.Orb
import Sts2Model.Model.Player
import Sts2Model.Model.State

import Sts2Model.Hook.Registry
import Sts2Model.Hook.ModHelper
import Sts2Model.Hook.Pipeline

import Sts2Model.Command.CreatureCmd
import Sts2Model.Command.CardCmd
import Sts2Model.Command.PowerCmd
import Sts2Model.Command.OrbCmd
import Sts2Model.Command.AttackCommand

import Sts2Model.Combat.MonsterAI
import Sts2Model.Combat.GameAction
import Sts2Model.Combat.TurnLoop

import Sts2Model.Multiplayer.ActionQueueSet
import Sts2Model.Replay.History
import Sts2Model.Sim.EffectIR
import Sts2Model.Sim.VanillaEffects
import Sts2Model.Replay.Timeline
import Sts2Model.Replay.TraceCodec

import Sts2Model.Mechanics.Orbs
import Sts2Model.Mechanics.Necrobinder
import Sts2Model.Mechanics.Regent
import Sts2Model.Mechanics.Fool
import Sts2Model.Mechanics.Dread

import Sts2Model.Run.Map
import Sts2Model.Run.Odds
import Sts2Model.Run.RunLoop

import Sts2Model.Proofs.DamagePipeline
import Sts2Model.Proofs.HookSafety
import Sts2Model.Proofs.CardPiles
import Sts2Model.Proofs.PowerSystem
import Sts2Model.Proofs.TurnMachine
import Sts2Model.Proofs.Determinism
import Sts2Model.Proofs.Mechanics
import Sts2Model.Proofs.MapTopology
import Sts2Model.Proofs.ReplayTimeline

import Sts2Model.Catalog.Types
import Sts2Model.Catalog.Cards
import Sts2Model.Catalog.Relics
import Sts2Model.Catalog.Powers
import Sts2Model.Catalog.Verify

-- Downstream Reference Examples (non-core; never imported by core modules)
import Sts2Model.Examples.VanillaShowcase
import Sts2Model.Examples.ModTemplates
import Sts2Model.Examples.TimelineShowcase
import Sts2Model.Examples.ReplayAnalyzerExample

namespace Sts2Model

def projectVersion : String := "0.1.0"

end Sts2Model
