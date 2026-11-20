using System.Globalization;

namespace Sts2Oracle;

public static partial class Program
{
    private enum ExpeditionPhase { Map, Room, Combat, Rewards, ActComplete, FinalEvent, Won, Lost, Abandoned }
    private enum ExpeditionRoom { Event, Monster, Boss }
    private readonly record struct ExpeditionCoord(int Column, int Row);
    private sealed record ExpeditionPoint(ExpeditionRoom Room, params ExpeditionCoord[] Children);
    private sealed record ExpeditionMap(ExpeditionCoord Start, ExpeditionCoord Boss, ExpeditionCoord? SecondBoss,
        Dictionary<ExpeditionCoord, ExpeditionPoint> Points);
    private abstract record ExpeditionOffer;
    private sealed record ExpeditionGold(int Amount) : ExpeditionOffer;
    private sealed record ExpeditionCards(params TCard[] Cards) : ExpeditionOffer;
    // One alternative is an ordinary independent reward. Multiple alternatives share one slot.
    private sealed record ExpeditionReward(params ExpeditionOffer[] Alternatives);

    // This reference drives source-level transitions for the explicit fixture below. Room types,
    // enemies, reward contents and maps are inputs, not predictions about world generation.
    private sealed class ExpeditionReferenceRun(ExpeditionMap map, List<TCard> deck, int actCount, int hp = 53)
    {
        private const decimal BaseMonsterOdds = 0.10m;
        private ExpeditionMap _map = map;
        private readonly RngOracle _shuffle = new(0x2222222222222222UL);
        private readonly RngOracle _combatTargets = new(0x8888888888888888UL);
        private int _nextInstanceId = 1000;
        private ExpeditionRoom? _parent;
        private bool _resumeParent;
        private ExpeditionReward?[] _rewards = [];

        public ExpeditionPhase Phase { get; private set; } = ExpeditionPhase.Map;
        public ExpeditionRoom? Room { get; private set; }
        public TSimState? Combat { get; private set; }
        public int Hp { get; private set; } = hp;
        public int MaxHp { get; private set; } = 75;
        public int Gold { get; private set; } = 99;
        public int TotalFloors { get; private set; }
        public int Act { get; private set; }
        public decimal MonsterOdds { get; private set; } = 0.50m;
        public List<ExpeditionCoord> Visited { get; } = [];
        public ExpeditionCoord Coord => Visited.Count == 0 ? _map.Start : Visited[^1];
        public IReadOnlyList<TCard> Deck => deck;
        public int PendingRewards => _rewards.Count(static reward => reward != null);
        public bool NavigationReset => Visited.Count == 0 && Coord == _map.Start && MonsterOdds == BaseMonsterOdds;

        // NMapScreen enables child points; RunManager.EnterMapCoord records one visit.
        // RunState.TotalFloor counts history entries, not a coordinate's row.
        public bool EnterPoint(ExpeditionCoord coord)
        {
            if (Phase != ExpeditionPhase.Map || !_map.Points.TryGetValue(coord, out var point) || Visited.Contains(coord))
                return false;
            if (Visited.Count == 0 ? coord != _map.Start : !_map.Points[Coord].Children.Contains(coord))
                return false;
            Visited.Add(coord);
            TotalFloors++;
            Room = point.Room;
            Phase = ExpeditionPhase.Room;
            return true;
        }

        public bool LeaveEvent()
        {
            if (Phase != ExpeditionPhase.Room || Room != ExpeditionRoom.Event) return false;
            Phase = ExpeditionPhase.Map;
            Room = null;
            return true;
        }

        public bool EnterCombatChild()
        {
            if (Phase != ExpeditionPhase.Room || Room != ExpeditionRoom.Event) return false;
            _parent = Room;
            Room = ExpeditionRoom.Monster;
            return true;
        }

        private bool InCombatRoom => Phase == ExpeditionPhase.Room && Room is ExpeditionRoom.Monster or ExpeditionRoom.Boss;

        // Player.PopulateCombatState clones the permanent cards and shuffles the draw pile;
        // CombatManager does a first-turn setup with fresh energy, orbs and an opening draw.
        public bool StartFight(int enemyHp, string enemyEntry, params ExpeditionReward?[] rewards)
        {
            if (!InCombatRoom || enemyHp <= 0) return false;
            var cards = new List<TCard>(deck.Count);
            foreach (var permanent in deck)
            {
                var copy = permanent.Clone();
                copy.InstId = _nextInstanceId++;
                copy.IsDupe = false;
                copy.CombatCostDelta = 0;
                cards.Add(copy);
            }
            var player = new TPlayer
            {
                Pid = 1, Cid = PlayerCreatureId, BaseMaxEnergy = 3, TurnNumber = 1, OrbCapacity = 3,
                Draw = RngOracle.UnstableShuffleGeneric(cards, _shuffle)
            };
            var fighting = new TSimState
            {
                ActIndex = Act, Gold = Gold, TotalFloors = TotalFloors,
                Rng = _combatTargets, NextInstanceId = _nextInstanceId, Players = [player],
                Creatures =
                [
                    new TCreature { Id = PlayerCreatureId, Entry = "DEFECT", Side = 1, Pid = 1, Hp = Hp, MaxHp = MaxHp },
                    new TCreature { Id = EnemyCreatureId, Entry = enemyEntry, Side = 2, Hp = enemyHp, MaxHp = enemyHp }
                ]
            };
            _rewards = rewards;
            Phase = ExpeditionPhase.Combat;
            Combat = fighting;
            RunSideTurnStartLifecycle(fighting, 1);
            if (fighting.IsInProgress)
            {
                player.Energy = player.BaseMaxEnergy;
                WireDrawCards(fighting, player, 5);
            }
            ObserveCombatEnd(fighting);
            return true;
        }

        public bool Play(string entry, int? target)
        {
            if (Phase != ExpeditionPhase.Combat || Combat is not { } fighting ||
                fighting.FindP(1)?.Hand.Find(card => card.Entry == entry) is not { } cardInHand ||
                !TryPlayCombatCard(fighting, 1, cardInHand.InstId, target, includeTier2: true)) return false;
            ObserveCombatEnd(fighting);
            return true;
        }

        public bool EndTurn()
        {
            if (Phase != ExpeditionPhase.Combat || Combat is not { } fighting) return false;
            RunRound(fighting, RunTier1Monster);
            ObserveCombatEnd(fighting);
            return true;
        }

        private void ObserveCombatEnd(TSimState fighting)
        {
            if (fighting.IsInProgress) return;
            // Read the engine's ended state before dropping it. Pending loss does not
            // run the victory path (CombatManager.ProcessPendingLoss / EndCombatInternal).
            var creature = fighting.FindC(PlayerCreatureId)!;
            Hp = creature.Hp;
            MaxHp = creature.MaxHp;
            _nextInstanceId = fighting.NextInstanceId;
            Combat = null; // Player.AfterCombatEnd: no fight-local piles, modifiers, powers or block survive.
            if (Hp > 0) Phase = ExpeditionPhase.Rewards;
            else
            {
                Phase = ExpeditionPhase.Lost;
                _rewards = [];
            }
        }

        // CombatRoom.StartPreFinishedCombat goes straight to room-end rewards. The
        // restored stack has already entered its map point; do not replay it or the fight.
        public bool RestoreRewards(bool resumeParent, params ExpeditionReward?[] populated)
        {
            if (!InCombatRoom || (resumeParent && _parent == null)) return false;
            _rewards = populated;
            _resumeParent = resumeParent;
            Phase = ExpeditionPhase.Rewards;
            return true;
        }

        private ExpeditionReward? RewardAt(int slot) =>
            Phase == ExpeditionPhase.Rewards && (uint)slot < (uint)_rewards.Length ? _rewards[slot] : null;

        private ExpeditionOffer? Available(int slot, int option)
        {
            if (RewardAt(slot) is not { } reward || (uint)option >= (uint)reward.Alternatives.Length) return null;
            return reward.Alternatives[option];
        }

        // GoldReward.OnSelect gains gold. CardReward.OnSelect adds the chosen card to Deck.
        // Reward.SelectUnsynchronized notifies the linked parent: the other offers close too.
        public bool ClaimGold(int slot, int option = 0)
        {
            if (Available(slot, option) is not ExpeditionGold gold) return false;
            Gold += gold.Amount;
            _rewards[slot] = null;
            return true;
        }

        public bool ChooseCard(int slot, int index, int option = 0)
        {
            if (Available(slot, option) is not ExpeditionCards cards || (uint)index >= (uint)cards.Cards.Length)
                return false;
            var selected = cards.Cards[index].Clone();
            selected.InstId = _nextInstanceId++;
            deck.Add(selected);
            _rewards[slot] = null;
            return true;
        }

        public bool SkipReward(int slot)
        {
            // CardReward.OnSkipped leaves the permanent deck untouched.
            if (RewardAt(slot) == null) return false;
            _rewards[slot] = null;
            return true;
        }

        public bool LeaveRewards()
        {
            if (Phase != ExpeditionPhase.Rewards || PendingRewards != 0) return false;
            // RunManager.ProceedFromTerminalRewardsScreenAsync may resume the parent event.
            // The last boss point is the second boss when present (CombatManager.EndCombatInternal).
            if (_resumeParent)
            {
                Phase = ExpeditionPhase.Room;
                Room = _parent;
            }
            else
            {
                var lastBoss = _map.SecondBoss ?? _map.Boss;
                Phase = Room == ExpeditionRoom.Boss && Coord == lastBoss ? ExpeditionPhase.ActComplete : ExpeditionPhase.Map;
                Room = null;
            }
            _parent = null;
            _resumeParent = false;
            _rewards = [];
            return true;
        }

        public bool EnterNextAct(ExpeditionMap next)
        {
            if (Phase != ExpeditionPhase.ActComplete || Act + 1 >= actCount) return false;
            // RunManager.SetActInternal clears this act's visits and resets unknown-point odds.
            Act++;
            _map = next;
            Visited.Clear();
            MonsterOdds = BaseMonsterOdds;
            Phase = ExpeditionPhase.Map;
            return true;
        }

        public bool EnterFinalEvent()
        {
            if (Phase != ExpeditionPhase.ActComplete || Act + 1 != actCount) return false;
            // RunManager.EnterNextAct opens TheArchitect, which separately calls WinRun.
            Room = ExpeditionRoom.Event;
            Phase = ExpeditionPhase.FinalEvent;
            return true;
        }

        public bool ConfirmVictory()
        {
            if (Phase != ExpeditionPhase.FinalEvent) return false;
            Phase = ExpeditionPhase.Won;
            return true;
        }

        public bool Abandon()
        {
            if (Phase is ExpeditionPhase.Won or ExpeditionPhase.Lost or ExpeditionPhase.Abandoned) return false;
            Phase = ExpeditionPhase.Abandoned;
            Combat = null;
            _rewards = [];
            return true;
        }
    }

    private static string EvalExpeditionReference()
    {
        var start = new ExpeditionCoord(3, 0);
        var roomA = new ExpeditionCoord(2, 1);
        var roomB = new ExpeditionCoord(2, 2);
        var boss = new ExpeditionCoord(3, 3);
        var secondBoss = new ExpeditionCoord(3, 4);
        var dangling = new ExpeditionCoord(4, 2);
        var map1 = new ExpeditionMap(start, boss, secondBoss, new()
        {
            [start] = new(ExpeditionRoom.Event, roomA),
            [roomA] = new(ExpeditionRoom.Monster, roomB, dangling),
            [roomB] = new(ExpeditionRoom.Monster, boss),
            [boss] = new(ExpeditionRoom.Boss, secondBoss),
            [secondBoss] = new(ExpeditionRoom.Boss)
        });
        var map2 = new ExpeditionMap(start, boss, null, new()
        {
            [start] = new(ExpeditionRoom.Event, boss), [boss] = new(ExpeditionRoom.Boss)
        });
        var strike = new TCard { InstId = 1, Entry = "STRIKE_DEFECT", CardType = "attack", Cost = 1, BaseDamage = 6 };
        var defend = new TCard { InstId = 2, Entry = "DEFEND_DEFECT", CardType = "skill", Cost = 1, BaseBlock = 5, GainsBlock = true };
        var capacitor = new TCard { Entry = "CAPACITOR", CardType = "power", Cost = 1 };

        ExpeditionReferenceRun NewRun(int hp = 53) => new(map1, [strike, defend], actCount: 2, hp: hp);
        static void Require(bool accepted, string action)
        {
            if (!accepted) throw new InvalidOperationException($"EXPEDITION: {action} failed");
        }
        void WinBoss(ExpeditionReferenceRun route, ExpeditionCoord coord)
        {
            Require(route.EnterPoint(coord), "enter boss");
            Require(route.StartFight(6, "CULTIST"), "start boss");
            Require(route.Play(strike.Entry, EnemyCreatureId), "strike boss");
            Require(route.LeaveRewards(), "leave boss rewards");
        }
        static int B(bool value) => value ? 1 : 0;
        static string Fields(params int[] values) => string.Join(',', values.Select(static n => n.ToString(CultureInfo.InvariantCulture)));

        var run = NewRun();
        int initialGold = run.Gold;
        Require(run.EnterPoint(start) && run.LeaveEvent() && run.EnterPoint(roomA), "enter A");
        Require(run.StartFight(6, "CULTIST", new ExpeditionReward(new ExpeditionGold(12)),
            new ExpeditionReward(new ExpeditionCards(strike, capacitor))), "start A");
        Require(run.Play(defend.Entry, PlayerCreatureId), "defend in A");
        int blockA = run.Combat!.FindC(PlayerCreatureId)!.Block;
        Require(run.Play(strike.Entry, EnemyCreatureId) && run.Phase == ExpeditionPhase.Rewards && run.Combat == null, "win A");
        bool leavePendingRejected = !run.LeaveRewards();
        bool outOfRangeRejected = !run.ChooseCard(1, 2);
        Require(run.ClaimGold(0), "claim gold in A");
        bool duplicateGoldRejected = !run.ClaimGold(0);
        Require(run.ChooseCard(1, 1), "take CAPACITOR");
        bool duplicateCardRejected = !run.ChooseCard(1, 0);
        string a = Fields(initialGold, blockA, run.Gold, B(outOfRangeRejected), B(duplicateGoldRejected),
            B(duplicateCardRejected), B(leavePendingRejected));

        Require(run.LeaveRewards(), "leave A rewards");
        bool danglingRejected = !run.EnterPoint(dangling);
        bool absentEdgeRejected = !run.EnterPoint(boss);
        Require(run.EnterPoint(roomB), "enter B");
        Require(run.StartFight(6, "CULTIST", new ExpeditionReward(new ExpeditionCards(strike))), "start B");
        var combatB = run.Combat!;
        var fighterB = combatB.FindC(PlayerCreatureId)!;
        var playerB = combatB.FindP(1)!;
        int hpB = fighterB.Hp, maxHpB = fighterB.MaxHp, blockB = fighterB.Block;
        int beforeOrbs = playerB.OrbCapacity;
        int energyB = playerB.Energy;
        int openingHand = playerB.Hand.Count;
        int deckSize = run.Deck.Count;
        int capCopies = run.Deck.Count(card => card.Entry == capacitor.Entry);
        bool fresh = playerB.Draw.Count == 0 && playerB.Discard.Count == 0 && playerB.Play.Count == 0 &&
            playerB.Exhaust.Count == 0 && playerB.Hand.All(card => card.CombatCostDelta == 0 &&
                run.Deck.All(permanent => permanent.InstId != card.InstId)) && fighterB.Powers.Count == 0;
        Require(Tier2OracleData.Cards.ContainsKey(capacitor.Entry), "generated CAPACITOR");
        Require(run.Play(capacitor.Entry, PlayerCreatureId), "play CAPACITOR in B");
        int afterOrbs = playerB.OrbCapacity;
        Require(run.Play(strike.Entry, EnemyCreatureId) && run.SkipReward(0), "win B and skip its card reward");
        bool skipRejected = !run.ChooseCard(0, 0);
        string b = Fields(hpB, maxHpB, blockB, energyB, openingHand, beforeOrbs, afterOrbs, deckSize, capCopies,
            B(fresh), B(skipRejected), run.Deck.Count);
        Require(run.LeaveRewards(), "leave B rewards");

        WinBoss(run, boss);
        bool firstBossBlocksAct = run.Phase == ExpeditionPhase.Map && !run.EnterNextAct(map2);
        WinBoss(run, secondBoss);
        int firstActFloors = run.TotalFloors;
        Require(run.EnterNextAct(map2), "enter second act");
        bool actReset = run.NavigationReset && run.TotalFloors == firstActFloors;
        Require(run.EnterPoint(start) && run.LeaveEvent(), "second act entrance");
        WinBoss(run, boss);
        bool earlyVictoryRejected = !run.ConfirmVictory();
        Require(run.EnterFinalEvent(), "enter final event");
        bool finalEvent = run.Phase == ExpeditionPhase.FinalEvent;
        Require(run.ConfirmVictory(), "confirm victory");
        string route = Fields(B(danglingRejected), B(absentEdgeRejected), B(firstBossBlocksAct), firstActFloors,
            B(actReset), B(earlyVictoryRejected), B(finalEvent), run.TotalFloors, B(run.Phase == ExpeditionPhase.Won), B(!run.Abandon()));

        var restored = NewRun();
        Require(restored.EnterPoint(start), "enter event with child");
        bool wrongPhaseRejected = !restored.EnterPoint(roomA);
        Require(restored.EnterCombatChild(), "enter combat child");
        Require(restored.RestoreRewards(true, new ExpeditionReward(new ExpeditionGold(2), new ExpeditionCards(defend))),
            "restore pre-finished combat");
        int restoreFloor = restored.TotalFloors;
        bool restoreNoReplay = restored.Combat == null && !restored.StartFight(6, "CULTIST");
        Require(restored.ClaimGold(0), "claim linked gold");
        bool linkedRejected = !restored.ChooseCard(0, 0, 1);
        Require(restored.LeaveRewards(), "resume parent after child rewards");
        bool resumedParent = restored.Phase == ExpeditionPhase.Room && restored.Room == ExpeditionRoom.Event &&
            restored.Visited.Count == 1 && restored.Visited[0] == start;
        string restore = Fields(B(wrongPhaseRejected), restoreFloor, B(restoreNoReplay), restored.Gold,
            B(linkedRejected), B(resumedParent));

        var lost = NewRun(hp: 1);
        Require(lost.EnterPoint(start) && lost.LeaveEvent() && lost.EnterPoint(roomA), "enter lethal encounter room");
        // COOP_GUARDIAN is the shared deterministic move fixture, not a generated encounter.
        Require(lost.StartFight(80, "COOP_GUARDIAN", new ExpeditionReward(new ExpeditionGold(12))), "start lethal encounter");
        Require(lost.EndTurn(), "end turn against COOP_GUARDIAN");
        string defeat = Fields(lost.Hp, lost.Gold, lost.PendingRewards, B(lost.Phase == ExpeditionPhase.Lost && !lost.ClaimGold(0)));

        return string.Join('|', a, b, route, restore, defeat);
    }
}
