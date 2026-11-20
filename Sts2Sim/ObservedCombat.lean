import Sts2Model.Replay.TraceCodec
import Sts2Model.Sim.VanillaEffects

namespace Sts2Sim.ObservedCombat

open Lean Sts2Model.Core Sts2Model.Model Sts2Model.Multiplayer Sts2Model.Replay Sts2Model.Sim

private structure Selection where
  playerId : Nat
  choiceId : Nat
  cards : List Nat
  deriving FromJson, ToJson

private structure Input where
  trace : WireTraceBundle
  playerId : Nat
  nextChoiceId : Nat
  initialPlay : Option (List WireCard) := none
  initialChoices : Option (List Selection) := none
  deriving FromJson

private def prepare (input : Input) : Except String (TimelineState × List TimelineEvent) := do
  unless input.trace.schemaVersion == traceSchemaVersion do throw "unsupported combat projection trace schema"
  let base ← decodeTimelineState input.trace.initialState
  let some cs := base.combat | throw "combat observation requires an initial combat"
  unless (cs.findPlayer input.playerId).isSome do throw "observation player is not in the initial combat"
  let play ← (input.initialPlay.getD []).mapM decodeCard
  let events ← input.trace.events.mapM decodeTimelineEvent
  let cs' := cs.updatePlayer input.playerId fun p =>
    { p with combatState := p.combatState.map fun pcs => { pcs with piles.play := play } }
  let sync := { base.choiceSync with
    nextChoiceIds := (input.playerId, input.nextChoiceId) :: base.choiceSync.nextChoiceIds.filter (·.1 != input.playerId) }
  pure ({ base with
    combat := some cs', choiceSync := sync
    choiceStream := (input.initialChoices.getD []).map (fun c => (c.playerId, c.choiceId, .cards c.cards)) }, events)

private def combatJson (cs : CombatState) : Json :=
  let snapshot := encodeCombatSnapshot cs
  let players := List.zipWith (fun wire (p : Player) =>
    let play := (p.combatState.map (·.piles.play)).getD []
    (toJson wire).setObjValAs! "play" (play.map encodeCard)) snapshot.players cs.players
  (toJson { snapshot with players := [] }).setObjValAs! "players" players

private def pendingJson (st : TimelineState) (p : PendingCardChoice) : Json :=
  let pid := p.play.playerId
  let action := (st.queueSet.queues.find? (·.ownerId == pid)).bind (·.actions.head?)
  Json.mkObj [("playerId", toJson pid), ("choiceId", toJson p.choiceId),
    ("actionId", toJson (action.map (·.actionId))), ("candidates", toJson p.candidates),
    ("automatic", toJson p.automatic)]

private def frame (step : Nat) (st : TimelineState) : Json :=
  let choices := st.choiceStream.filterMap fun (pid, cid, r) =>
    match r with | .cards ids => some (toJson (⟨pid, cid, ids⟩ : Selection)) | _ => none
  Json.mkObj [("step", toJson step), ("combat", toJson (st.combat.map combatJson)),
    ("choices", toJson choices), ("pending", toJson (st.pendingCards.map (pendingJson st)))]

private def accepts (st : TimelineState) (pid : PlayerId) (id : Nat) (r : ChoiceResult) : Bool :=
  st.combat.any fun cs => st.pendingCards.any fun p => p.accepts cs pid id r

private def replay (base : TimelineState) (events : List TimelineEvent) : Except String Json := do
  let mut st := base
  let mut frames := #[frame 0 st]
  for ev in events do
    if let .combat ce := ev.kind then
      if ce.eventType == .playerChoice then
        let pid := ce.playerId.getD ev.actorPlayerId
        let id := ce.choiceId.getD 0
        let res := ce.choiceResult.getD .skipped
        unless accepts st pid id res && !st.choiceStream.any (fun (p, i, _) => p == pid && i == id) do
          throw s!"step {ev.seqIdx}: invalid or unreserved card choice for player {pid}, choice {id}"
    st := replayStep fullVanillaEffectEnv st ev
    if let some err := st.cardChoiceError then throw s!"step {ev.seqIdx}: {err}"
    frames := frames.push (frame ev.seqIdx st)
  unless st.pendingCards.isEmpty do throw "unfinished card choice"
  pure (Json.mkObj [("frames", toJson frames)])

def run (file : String) : IO UInt32 := do
  let raw ← try IO.FS.readFile file catch err =>
    IO.eprintln s!"{file}: {err}"
    return 2
  let prepared : Except String (TimelineState × List TimelineEvent) := do
    let input : Input ← (Json.parse raw).bind fromJson?
    prepare input
  match prepared with
  | .error e => IO.eprintln e; return 2
  | .ok (base, events) =>
      match replay base events with
      | .error e => IO.eprintln e; return 1
      | .ok result => IO.println result.compress; return 0

end Sts2Sim.ObservedCombat
