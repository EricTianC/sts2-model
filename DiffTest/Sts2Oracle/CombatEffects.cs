using System.Globalization;

namespace Sts2Oracle;

public static partial class Program
{
    private const int PlayerCreatureId = 101;
    private const int EnemyCreatureId = 200;
    private const ValuePropFlags UnpoweredDamage = ValuePropFlags.Unpowered;

    // TIMELINE_SEEK, TRACE_JSON, and both effect fixtures share combat phases.
    // The caller owns replay bookkeeping, including the checksum step ID.
    private static void RunRound(TSimState st, Action<TSimState, TCreature> runMonster)
    {
        if (!st.IsInProgress) return;
        RunSideTurnEndLifecycle(st, 1);
        if (!st.IsInProgress) return;
        foreach (var p in st.Players)
        {
            p.Discard.AddRange(p.Hand);
            p.Hand.Clear();
        }
        st.Side = 2;
        foreach (var c in st.Creatures)
            if (c.Side == 2 && !c.HasPower("BARRICADE_POWER")) c.Block = 0;
        RunSideTurnStartLifecycle(st, 2);
        if (!st.IsInProgress) return;
        foreach (var enemy in st.Creatures.Where(c => c.Side == 2 && c.Hp > 0).ToArray())
        {
            if (!st.IsInProgress) break;
            if (enemy.Hp > 0) runMonster(st, enemy);
        }
        TCheckWin(st);
        if (!st.IsInProgress) return;
        RunSideTurnEndLifecycle(st, 2);
        if (!st.IsInProgress) return;
        foreach (var p in st.Players) p.TurnNumber++;
        st.RoundNumber++;
        st.Side = 1;
        foreach (var c in st.Creatures)
            if (c.Side == 1 && !c.HasPower("BARRICADE_POWER") &&
                (c.Pid is not int pid || st.FindP(pid)?.TurnNumber != 1))
                c.Block = 0;
        foreach (var p in st.Players)
        {
            p.Energy = p.BaseMaxEnergy;
            WireDrawCards(st, p, 5);
        }
        RunSideTurnStartLifecycle(st, 1);
    }

    private static void LogMove(TCreature enemy, string move)
    {
        enemy.MoveId = move;
        enemy.StateLog.Add(move);
    }

    private static void RunTier1Monster(TSimState st, TCreature enemy) => TryRunTier1Monster(st, enemy);

    private static bool TryRunTier1Monster(TSimState st, TCreature enemy)
    {
        bool first = enemy.StateLog.Count == 0;
        string Initially(string move) => enemy.MoveId.Length == 0 ? move : enemy.MoveId;
        switch (enemy.Entry)
        {
            case "COOP_GUARDIAN":
                LogMove(enemy, first ? Initially("SLAM") : enemy.MoveId == "SLAM" ? "FORTIFY" : "SLAM");
                if (enemy.MoveId == "SLAM")
                    DamageAllies(st, enemy.Id, 7);
                else
                {
                    WireGainBlock(st, enemy.Id, 8, ValuePropFlags.Move);
                    WireApplyPower(st, enemy.Id, "STRENGTH_POWER", false, true, 1);
                }
                return true;
            case "CULTIST":
                LogMove(enemy, first ? Initially("INCANT") : "DARK_STRIKE");
                if (enemy.MoveId == "INCANT")
                    WireApplyPower(st, enemy.Id, "STRENGTH_POWER", false, true, 3);
                else if (LivingPlayerOrAlly(st) is { } ally)
                    TApplyDamageHit(st, enemy.Id, ally.Id, 6, ValuePropFlags.Move);
                return true;
            default:
                return false;
        }
    }

    private static TCreature? FirstLivingPlayer(TSimState st) => st.Creatures.Find(c => c.Side == 1 && c.Pid.HasValue && c.Hp > 0);
    private static TCreature? LivingPlayerOrAlly(TSimState st) =>
        FirstLivingPlayer(st) ?? st.Creatures.Find(c => c.Side == 1 && c.Hp > 0);

    private static void DamageAllies(TSimState st, int actor, decimal amount)
    {
        foreach (var c in st.Creatures)
            if (c.Side == 1 && c.Hp > 0) TApplyDamageHit(st, actor, c.Id, amount, ValuePropFlags.Move);
    }

    private static void RunLifecycleMonster(TSimState st, TCreature enemy)
    {
        switch (enemy.Entry)
        {
            case "LC_ATK_VULN":
                LogMove(enemy, "HIT");
                DamageAllies(st, enemy.Id, 5);
                foreach (var c in st.Creatures)
                    if (c.Side == 1 && c.Hp > 0)
                        WireApplyPower(st, c.Id, "VULNERABLE_POWER", true, false, 1);
                break;
            case "LC_RITUAL":
                if (enemy.StateLog.Count == 0)
                {
                    LogMove(enemy, "BUFF");
                    WireApplyPower(st, enemy.Id, "RITUAL_POWER", false, false, 2);
                }
                else
                {
                    LogMove(enemy, "HIT");
                    DamageAllies(st, enemy.Id, 4);
                }
                break;
            case "LC_DEBUFF":
                LogMove(enemy, "HEX");
                ApplyToAllies(st, "WEAK_POWER");
                ApplyToAllies(st, "FRAIL_POWER");
                break;
            case "LC_PASS":
                LogMove(enemy, "NOP");
                break;
        }
    }

    private static void ApplyToAllies(TSimState st, string entry)
    {
        foreach (var c in st.Creatures)
            if (c.Side == 1 && c.Hp > 0) WireApplyPower(st, c.Id, entry, true, false, 1);
    }

    private static string DiffField(string[] f, int i, string fallback = "") => i < f.Length ? f[i] : fallback;
    private static int DiffInt(string s) => int.TryParse(s, NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture, out int value) ? value : 0;
    private static int DiffNat(string[] f, int i, int fallback = 0) => i >= f.Length ? fallback :
        int.TryParse(f[i], NumberStyles.None, CultureInfo.InvariantCulture, out int value) ? value : 0;

    private static List<TPower> ParseDiffPowers(string field, int firstId)
    {
        var powers = new List<TPower>();
        foreach (string token in field.Split(',', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries))
        {
            string[] parts = token.Split(':');
            string entry = parts[0];
            powers.Add(new TPower
            {
                InstId = firstId + powers.Count, Entry = entry,
                Amt = parts.Length > 1 ? DiffInt(parts[1]) : 1,
                IsDebuff = entry is "VULNERABLE_POWER" or "WEAK_POWER" or "FRAIL_POWER" or "POISON_POWER" or "DOOM_POWER",
                AllowNeg = entry is "STRENGTH_POWER" or "DEXTERITY_POWER" or "FOCUS_POWER",
                IsSingle = entry == "BARRICADE_POWER"
            });
        }
        return powers;
    }

    private static string FormatDiffPowers(List<TPower> powers) => powers.Count == 0 ? "-" :
        string.Join(';', powers.Select(p => $"{p.Entry}:{p.Amt}:{(p.SkipNextDurationTick ? 1 : 0)}"));

    private static TOrb DefaultOrb(int id, string kind)
    {
        var (tag, passive, evoke) = kind switch
        {
            "frost" => ("frost", 2, 5), "dark" => ("dark", 6, 6), "plasma" => ("plasma", 1, 2),
            "glass" => ("glass", 4, 8), _ => ("lightning", 3, 8)
        };
        return new TOrb { InstId = id, Kind = tag, BasePassive = passive, BaseEvoke = evoke };
    }

    private static TSimState DiffCombat(ulong seed, int asc, TPlayer player, TCreature ally, TCreature enemy) => new()
    {
        Rng = new RngOracle(seed), NextInstanceId = 2000, AscensionLevel = asc,
        Players = [player], Creatures = [ally, enemy]
    };

    private static List<TCard> StarterCards(int first, int count, string entry) =>
        Enumerable.Range(first, count).Select(id => new TCard { InstId = id, Entry = entry, Cost = 1 }).ToList();

    private static string EvalTurnLifecycle(string[] f)
    {
        var (entry, move) = DiffNat(f, 1) switch
        {
            1 => ("LC_ATK_VULN", "HIT"), 2 => ("LC_RITUAL", "BUFF"),
            3 => ("LC_DEBUFF", "HEX"), _ => ("LC_PASS", "NOP")
        };
        int pHp = DiffNat(f, 2, 80), eHp = DiffNat(f, 6, 40);
        var ally = new TCreature
        {
            Id = PlayerCreatureId, Side = 1, Pid = 1, Entry = "DEFECT", Hp = pHp, MaxHp = Math.Max(80, pHp),
            Block = DiffNat(f, 3), Powers = ParseDiffPowers(DiffField(f, 4), 10)
        };
        var enemy = new TCreature
        {
            Id = EnemyCreatureId, Side = 2, Entry = entry, MoveId = move, Hp = eHp, MaxHp = Math.Max(80, eHp),
            Block = DiffNat(f, 7), Powers = ParseDiffPowers(DiffField(f, 8), 50)
        };
        var p = new TPlayer
        {
            Pid = 1, Cid = ally.Id, Energy = 3, BaseMaxEnergy = 3, TurnNumber = 1,
            Draw = StarterCards(1001, 15, "STRIKE_IRONCLAD")
        };
        foreach (string token in DiffField(f, 5).Split(',', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries))
        {
            string[] parts = token.Split(':');
            var orb = DefaultOrb(1 + p.Orbs.Count, parts[0]);
            if (parts.Length > 1) orb.BasePassive = DiffInt(parts[1]);
            if (parts.Length > 2) orb.BaseEvoke = DiffInt(parts[2]);
            p.Orbs.Add(orb);
        }
        p.OrbCapacity = Math.Max(3, p.Orbs.Count);
        var st = DiffCombat(12345, 0, p, ally, enemy);
        foreach (string token in DiffField(f, 9).Split(';', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries))
        {
            if (!st.IsInProgress) break;
            switch (token)
            {
                case "P_STRIKE": case "P_UNPOW":
                    TApplyDamageHit(st, ally.Id, enemy.Id, 6, token == "P_STRIKE" ? ValuePropFlags.Move : UnpoweredDamage);
                    TCheckWin(st);
                    break;
                case "END_ROUND":
                    RunRound(st, RunLifecycleMonster);
                    break;
                default:
                    if (token.StartsWith("P_VULN:", StringComparison.Ordinal))
                        WireApplyPower(st, enemy.Id, "VULNERABLE_POWER", true, false, DiffInt(token.Split(':')[1]));
                    break;
            }
        }
        string orbs = p.Orbs.Count == 0 ? "-" : string.Join(';', p.Orbs.Select(o => $"{o.Kind}:{(int)o.BasePassive}:{(int)o.BaseEvoke}"));
        return $"{ally.Hp},{ally.Block},{p.Energy},{FormatDiffPowers(ally.Powers)}|{enemy.Hp},{enemy.Block},{(st.IsInProgress ? 1 : 0)},{FormatDiffPowers(enemy.Powers)}|{orbs}";
    }

    private static string EvalTier2Effects(string[] f)
    {
        string kind = DiffField(f, 1, "CARD"), entry = DiffField(f, 2);
        int param = DiffNat(f, 3), asc = DiffNat(f, 4), strength = DiffInt(DiffField(f, 5));
        int eHp = Math.Max(1, DiffNat(f, 6, 80));
        var ally = new TCreature
        {
            Id = PlayerCreatureId, Side = 1, Pid = 1, Entry = "DEFECT", Hp = 70, MaxHp = 80,
            Powers = ParseDiffPowers(DiffField(f, 8), 10)
        };
        if (strength != 0)
            ally.Powers.Insert(0, new TPower { InstId = 9, Entry = "STRENGTH_POWER", AllowNeg = true, Amt = strength });
        var enemy = new TCreature
        {
            Id = EnemyCreatureId, Side = 2, Entry = kind == "MONSTER" ? entry : "BIG_DUMMY",
            Hp = eHp, MaxHp = Math.Max(120, eHp), Block = DiffNat(f, 7), Powers = ParseDiffPowers(DiffField(f, 9), 50)
        };
        var p = new TPlayer
        {
            Pid = 1, Cid = ally.Id, Energy = 5, BaseMaxEnergy = 3, Stars = 2, TurnNumber = 1,
            Hand = StarterCards(1001, 5, "STRIKE_IRONCLAD"), Draw = StarterCards(1011, 10, "DEFEND_IRONCLAD"),
            Discard = StarterCards(1021, 2, "BASH")
        };
        var st = DiffCombat(424242, asc, p, ally, enemy);
        bool found = false;
        switch (kind)
        {
            case "CARD":
                found = Tier2OracleData.Cards.ContainsKey(entry);
                ExecCardEffect(st, p, new TCard { InstId = 999, Entry = entry, Cost = 1, UpgradeLevel = param > 0 ? 1 : 0 }, enemy.Id, includeTier2: true);
                TCheckWin(st);
                break;
            case "POTION":
                found = Tier2OracleData.Potions.ContainsKey(entry);
                ExecPotionEffect(st, p, entry, enemy.Id, includeTier2: true);
                TCheckWin(st);
                break;
            case "MONSTER":
                found = Tier2OracleData.Monsters.ContainsKey(entry);
                for (int i = 0; i < Math.Clamp(param, 1, 5) && st.IsInProgress; i++) RunRound(st, RunFullMonster);
                break;
        }
        string hand = p.Hand.Count == 0 ? "-" : string.Join(',', p.Hand.Select(c => c.Entry));
        int allies = st.Creatures.Count(c => c.Side == 1);
        return $"{ally.Hp},{ally.Block},{p.Energy},{p.Stars},{p.Hand.Count},{p.Draw.Count},{p.Discard.Count},{p.Exhaust.Count},{p.Orbs.Count},{allies}|" +
            $"{enemy.Hp},{enemy.Block},{enemy.MoveId},{(st.IsInProgress ? 1 : 0)}|{FormatDiffPowers(ally.Powers)}|{FormatDiffPowers(enemy.Powers)}|{hand}|found={(found ? 1 : 0)}";
    }

    // The caller owns replay bookkeeping; this is the shared card execution path.
    private static bool TryPlayCombatCard(TSimState st, int pid, int cid, int? target, bool includeTier2 = false)
    {
        if (st.FindP(pid) is not { } p || p.Hand.Find(c => c.InstId == cid) is not { } card) return false;
        int cost = card.CurrentCost;
        if (p.Energy < cost) return false;
        p.Energy -= cost;
        p.Hand.Remove(card);
        p.Play.Add(card);
        ExecCardEffect(st, p, card, target, includeTier2);
        p.Play.Remove(card);
        // CardModel.GetResultLocationForCardPlay: powers leave the combat piles.
        if (card.CardType != "power") (card.Exhausts ? p.Exhaust : p.Discard).Add(card);
        TCheckWin(st);
        return true;
    }

    private static string EvalTier2Card(string[] f)
    {
        const int cardId = 999, twinId = 998, fillerId = 1001, chosenAllyId = 102;
        string mode = f[1], entry = f[2], filler = f[12];
        if (!Tier2OracleData.Cards.ContainsKey(entry))
            throw new InvalidOperationException($"Missing generated card in TIER2_CARD: {entry}");
        int target = f[6] switch
        {
            "S" => PlayerCreatureId, "A" => chosenAllyId, "E" => EnemyCreatureId,
            _ => throw new InvalidOperationException($"Unknown TIER2_CARD target {f[6]}")
        };
        var template = new TCard
        {
            InstId = cardId, Entry = entry, UpgradeLevel = DiffNat(f, 3), Cost = DiffNat(f, 4),
            CardType = f[5], Exhausts = f[7] == "1"
        };
        // Fixed opening layout, not a claim about the native shuffle order.
        // Like Player.PopulateCombatState, only fight-local copies enter the piles.
        var deckHand = new List<TCard> { template };
        if (entry == "MODDED")
        {
            var twin = template.Clone();
            twin.InstId = twinId;
            deckHand.Add(twin);
        }
        if (filler != "-")
            deckHand.Add(new TCard
            {
                InstId = fillerId, Entry = filler == "attack" ? "STRIKE_IRONCLAD" : "DEFEND_IRONCLAD",
                CardType = filler, Cost = 1
            });
        var deckDraw = StarterCards(1011, 7, "DEFEND_IRONCLAD");
        foreach (var c in deckDraw) c.CardType = "skill";
        var deckDiscard = StarterCards(1021, DiffNat(f, 11), "BASH");
        foreach (var c in deckDiscard) c.Cost = 2;

        List<TPower> Powers(int column, int firstId) => ParseDiffPowers(f[column] == "-" ? "" : f[column], firstId);
        TSimState BeginCombat(bool fresh, int playerHp, int allyHp)
        {
            var me = new TCreature
            {
                Id = PlayerCreatureId, Side = 1, Pid = 1, Entry = "DEFECT", Hp = playerHp, MaxHp = 80,
                Block = fresh ? 0 : DiffNat(f, 9), Powers = fresh ? [] : Powers(15, 10)
            };
            var ally = new TCreature
            {
                Id = chosenAllyId, Side = 1, Pid = 2, Entry = "SILENT", Hp = allyHp, MaxHp = 80,
                Block = fresh ? 0 : DiffNat(f, 10), Powers = fresh ? [] : Powers(16, 30)
            };
            int enemyHp = !fresh && mode == "NEXT" ? 6 : 80;
            var enemy = new TCreature
            {
                Id = EnemyCreatureId, Side = 2, Entry = mode == "ROUND" ? "LC_PASS" : "BIG_DUMMY",
                Hp = enemyHp, MaxHp = enemyHp, Powers = fresh ? [] : Powers(17, 50)
            };
            var p = new TPlayer
            {
                Pid = 1, Cid = me.Id, Energy = fresh ? 3 : DiffNat(f, 8), BaseMaxEnergy = 3, TurnNumber = 1,
                OrbCapacity = fresh ? 3 : DiffNat(f, 13),
                Hand = deckHand.Select(c => c.Clone()).ToList(),
                Draw = deckDraw.Select(c => c.Clone()).ToList(),
                Discard = deckDiscard.Select(c => c.Clone()).ToList()
            };
            if (!fresh)
                foreach (var kind in f[14].Split(','))
                    if (kind != "-") p.Orbs.Add(DefaultOrb(1 + p.Orbs.Count, kind));
            return new TSimState
            {
                Rng = new RngOracle(424242), NextInstanceId = 2000,
                Players = [p, new TPlayer { Pid = 2, Cid = chosenAllyId, Energy = 3, BaseMaxEnergy = 3, TurnNumber = 1 }],
                Creatures = [me, ally, enemy]
            };
        }

        var st = BeginCombat(false, 70, 70);
        var player = st.Players[0];
        bool ok;
        if (mode == "EFFECT")
        {
            var card = player.Hand[0];
            player.Hand.RemoveAt(0);
            player.Play.Add(card);
            ExecCardEffect(st, player, card, target, includeTier2: true);
            ok = true;
        }
        else
        {
            ok = TryPlayCombatCard(st, 1, cardId, target, includeTier2: true);
            if (ok && mode == "ROUND") RunRound(st, RunLifecycleMonster);
            if (ok && mode == "NEXT")
            {
                if (!TryPlayCombatCard(st, 1, fillerId, EnemyCreatureId) || st.IsInProgress)
                    throw new InvalidOperationException("TIER2_CARD NEXT did not win the first encounter");
                st = BeginCombat(true, st.Creatures[0].Hp, st.Creatures[1].Hp);
                player = st.Players[0];
            }
        }

        static string Pile(List<TCard> pile) => pile.Count == 0 ? "-" :
            string.Join(',', pile.Select(c => $"{c.InstId}:{c.CurrentCost}"));
        var pc = st.Creatures[0];
        var ac = st.Creatures[1];
        var ec = st.Creatures[2];
        string orbs = player.Orbs.Count == 0 ? "-" : string.Join(',', player.Orbs.Select(o => o.Kind));
        return $"{(ok ? 1 : 0)}|{pc.Hp},{pc.Block},{player.Energy},{player.OrbCapacity}|{ac.Hp},{ac.Block}|{ec.Hp},{ec.Block}|" +
            $"{FormatDiffPowers(pc.Powers)}|{FormatDiffPowers(ac.Powers)}|{FormatDiffPowers(ec.Powers)}|{orbs}|" +
            $"{Pile(player.Hand)}|{Pile(player.Draw)}|{Pile(player.Discard)}|{Pile(player.Exhaust)}|{Pile(player.Play)}";
    }

    private static void ExecCardEffect(TSimState st, TPlayer p, TCard card, int? target, bool includeTier2 = false)
    {
        bool up = card.UpgradeLevel > 0;
        decimal Dmg(int amount) => card.BaseDamage == 0 ? amount : card.BaseDamage;
        int Blk(int amount) => card.BaseBlock == 0 ? amount : card.BaseBlock;
        void Damage(decimal amount, int hits = 1)
        {
            if (target is int id)
                for (int i = 0; i < hits; i++) TApplyDamageHit(st, p.Cid, id, amount, ValuePropFlags.Move);
        }
        void Block(int amount) => WireGainBlock(st, p.Cid, amount, ValuePropFlags.Move);
        void Debuff(string entry, int amount)
        {
            if (target is int id) WireApplyPower(st, id, entry, true, false, amount);
        }
        switch (card.Entry)
        {
            case "STRIKE_IRONCLAD": case "STRIKE_SILENT": case "STRIKE_DEFECT": case "STRIKE_NECROBINDER": case "STRIKE_REGENT":
                Damage(Dmg(up ? 9 : 6)); break;
            case "DEFEND_IRONCLAD": case "DEFEND_SILENT": case "DEFEND_DEFECT": case "DEFEND_NECROBINDER": case "DEFEND_REGENT":
                Block(Blk(up ? 8 : 5)); break;
            case "BASH":
                Damage(Dmg(up ? 10 : 8)); Debuff("VULNERABLE_POWER", up ? 3 : 2); break;
            case "TWIN_STRIKE":
                Damage(Dmg(up ? 7 : 5), 2); break;
            case "ANGER":
                Damage(Dmg(up ? 8 : 6));
                var dupe = card.Clone(); dupe.InstId += 50000; dupe.IsDupe = true; p.Discard.Add(dupe);
                break;
            case "POMMEL_STRIKE":
                Damage(Dmg(up ? 10 : 9)); WireDrawCards(st, p, up ? 2 : 1); break;
            case "IRON_WAVE":
                Block(Blk(up ? 7 : 5)); Damage(Dmg(up ? 7 : 5)); break;
            case "CLEAVE":
                foreach (var enemy in st.Creatures)
                    if (enemy.Side == 2 && enemy.Hp > 0) TApplyDamageHit(st, p.Cid, enemy.Id, Dmg(up ? 11 : 8), ValuePropFlags.Move);
                break;
            case "CLOTHESLINE":
                Damage(Dmg(up ? 14 : 12)); Debuff("WEAK_POWER", up ? 3 : 2); break;
            case "UPPERCUT":
                Damage(Dmg(13)); Debuff("WEAK_POWER", up ? 2 : 1); Debuff("VULNERABLE_POWER", up ? 2 : 1); break;
            case "SHOCKWAVE":
                foreach (var enemy in st.Creatures)
                    if (enemy.Side == 2 && enemy.Hp > 0) WireApplyPower(st, enemy.Id, "WEAK_POWER", true, false, up ? 5 : 3);
                foreach (var enemy in st.Creatures)
                    if (enemy.Side == 2 && enemy.Hp > 0) WireApplyPower(st, enemy.Id, "VULNERABLE_POWER", true, false, up ? 5 : 3);
                break;
            case "BLUDGEON":
                Damage(Dmg(up ? 42 : 32)); break;
            case "INFLAME":
                WireApplyPower(st, p.Cid, "STRENGTH_POWER", false, true, up ? 3 : 2); break;
            case "FOOTWORK":
                WireApplyPower(st, p.Cid, "DEXTERITY_POWER", false, true, up ? 3 : 2); break;
            case "NEUTRALIZE":
                Damage(Dmg(up ? 4 : 3)); Debuff("WEAK_POWER", up ? 2 : 1); break;
            case "SURVIVOR":
                Block(Blk(up ? 11 : 8)); MoveSelected(p, card, 1, p.Discard); break;
            case "SHRUG_IT_OFF":
                Block(Blk(up ? 11 : 8)); WireDrawCards(st, p, 1); break;
            case "POISONED_STAB":
                Damage(Dmg(up ? 8 : 6)); Debuff("POISON_POWER", up ? 4 : 3); break;
            case "ZAP":
                ChannelOrb(st, p, "lightning"); break;
            case "DUALCAST":
                EvokeOrb(st, p); EvokeOrb(st, p); break;
            case "SOVEREIGN_BLADE":
                Damage(Dmg(10)); break;
            case "STAR_STRIKE":
                Damage(Dmg(14)); break;
            default:
                if (includeTier2 && Tier2OracleData.Cards.TryGetValue(card.Entry, out var tier2))
                    ExecGeneratedOps(st, "CARD", card.Entry, up ? tier2.UpgradedOps : tier2.BaseOps, p.Cid, target, p, card);
                else if (card.CardType == "attack" && card.BaseDamage > 0) Damage(card.BaseDamage);
                else if (card.GainsBlock && card.BaseBlock > 0) Block(card.BaseBlock);
                break;
        }
    }

    private static void ExecPotionEffect(TSimState st, TPlayer p, string entry, int? target, bool includeTier2 = false)
    {
        switch (entry)
        {
            case "FIRE_POTION":
                if (target is int fireId) TApplyDamageHit(st, p.Cid, fireId, 20, UnpoweredDamage);
                break;
            case "BLOCK_POTION": WireGainBlock(st, p.Cid, 12, ValuePropFlags.Unpowered); break;
            case "STRENGTH_POTION": WireApplyPower(st, p.Cid, "STRENGTH_POWER", false, true, 2); break;
            case "FEAR_POTION":
                if (target is int fearId) WireApplyPower(st, fearId, "VULNERABLE_POWER", true, false, 3);
                break;
            case "WEAK_POTION":
                if (target is int weakId) WireApplyPower(st, weakId, "WEAK_POWER", true, false, 3);
                break;
            case "ENERGY_POTION": GainEnergy(p, 2); break;
            case "SWIFT_POTION": WireDrawCards(st, p, 3); break;
            case "HEAL_POTION": Heal(st, p.Cid, 10); break;
            default:
                if (includeTier2 && Tier2OracleData.Potions.TryGetValue(entry, out var tier2))
                    ExecGeneratedOps(st, "POTION", entry, tier2.Ops, p.Cid, target, p, null);
                break;
        }
    }

    private static void RunFullMonster(TSimState st, TCreature enemy)
    {
        if (TryRunTier1Monster(st, enemy) || !Tier2OracleData.Monsters.TryGetValue(enemy.Entry, out var monster)) return;
        string id = enemy.MoveId.Length == 0 ? monster.InitialStateId : enemy.MoveId;
        var node = Array.Find(monster.Nodes, n => n.Id == id);
        var rng = st.Rng;
        if (node != null && (node.IsRandomBranch || enemy.StateLog.Count != 0))
        {
            // A failed traversal does not advance the combat RNG.
            for (int fuel = 16; fuel > 0 && node != null; fuel--)
            {
                id = node.FollowUpId;
                if (node.IsRandomBranch)
                {
                    int weight = node.RandomTargets.Sum(t => t.Weight);
                    if (weight > 0)
                    {
                        if (rng == st.Rng) rng = rng.Clone();
                        int roll = rng.NextInt(weight);
                        foreach (var t in node.RandomTargets)
                        {
                            if (roll < t.Weight) { id = t.TargetId; break; }
                            roll -= t.Weight;
                        }
                    }
                }
                if (id.Length == 0) id = monster.InitialStateId;
                node = Array.Find(monster.Nodes, n => n.Id == id);
                if (node is { IsRandomBranch: false }) break;
            }
        }
        if (node is not { IsRandomBranch: false }) return;
        st.Rng = rng;
        LogMove(enemy, node.Id);
        var move = Array.Find(monster.Moves, m => m.MoveId == node.Id);
        if (move != null) ExecGeneratedOps(st, "MONSTER", monster.Id, move.Ops, enemy.Id, FirstLivingPlayer(st)?.Id, null, null);
    }

    private static int[] ResolveGeneratedTargets(TSimState st, string target, int actor, int? chosen) => target switch
    {
        "Self" => [actor],
        "ChosenTarget" => chosen is int id ? [id] : [],
        "AllEnemies" => st.Creatures.Where(c => c.Side == 2 && c.Hp > 0).Select(c => c.Id).ToArray(),
        "RandomEnemy" => RandomEnemy(st),
        "AllAllies" => st.Creatures.Where(c => c.Side == 1 && c.Hp > 0).Select(c => c.Id).ToArray(),
        "FirstLivingPlayer" => LivingPlayerOrAlly(st) is { } c ? [c.Id] : [],
        _ => throw new InvalidOperationException($"Unknown Tier-2 target: {target}")
    };

    private static int[] RandomEnemy(TSimState st)
    {
        var enemies = st.Creatures.Where(c => c.Side == 2 && c.Hp > 0).ToArray();
        return enemies.Length switch { 0 => [], 1 => [enemies[0].Id], _ => [enemies[st.Rng.NextInt(enemies.Length)].Id] };
    }

    private static void ExecGeneratedOps(TSimState st, string kind, string entry, T2Op[] ops, int actor,
        int? target, TPlayer? player, TCard? source)
    {
        foreach (var op in ops)
        {
            decimal AscAmount() => st.AscensionLevel >= op.AscThreshold ? op.AscValue : op.Amount;
            int[] Targets() => ResolveGeneratedTargets(st, op.Target, actor, target);
            decimal RuntimeValue()
            {
                decimal multiplierInput = op.StrArg switch
                {
                    "actorBlock" => st.FindC(actor)?.Block ?? 0,
                    "chosenBlock" => target is int id ? st.FindC(id)?.Block ?? 0 : 0,
                    "discardCount" => player?.Discard.Count ?? 0,
                    _ => throw new InvalidOperationException($"Unknown Tier-2 value source: {op.StrArg}")
                };
                return op.Amount + multiplierInput * op.Multiplier;
            }
            var damageProps = (op.Move ? ValuePropFlags.Move : ValuePropFlags.None) |
                (op.Unpowered ? ValuePropFlags.Unpowered : ValuePropFlags.None) |
                (op.Unblockable ? ValuePropFlags.Unblockable : ValuePropFlags.None);
            switch (op.Kind)
            {
                case "dealDamage": case "dealDamageAsc": case nameof(IrKind.DealDamageValue):
                    var targets = Targets();
                    decimal damage = op.Kind switch
                    {
                        "dealDamageAsc" => AscAmount(), nameof(IrKind.DealDamageValue) => RuntimeValue(), _ => op.Amount
                    };
                    for (int hit = 0; hit < op.Param1; hit++)
                        foreach (int id in targets) TApplyDamageHit(st, actor, id, damage, damageProps);
                    break;
                case nameof(IrKind.DealDamageIfPower):
                    foreach (int id in Targets())
                    {
                        // Select hit count once, before any damage hooks run.
                        int hits = st.FindC(id)?.HasPower(op.StrArg) == true ? op.Param1 : op.Param2;
                        for (int hit = 0; hit < hits; hit++) TApplyDamageHit(st, actor, id, op.Amount, damageProps);
                    }
                    break;
                case "gainBlock": case "gainBlockAsc": case nameof(IrKind.GainBlockValue):
                    var blockProps = op.Kind == nameof(IrKind.GainBlockValue)
                        ? damageProps
                        : op.Unpowered ? ValuePropFlags.Unpowered : ValuePropFlags.Move;
                    decimal block = op.Kind switch
                    {
                        "gainBlockAsc" => AscAmount(), nameof(IrKind.GainBlockValue) => RuntimeValue(), _ => op.Amount
                    };
                    foreach (int id in Targets()) WireGainBlock(st, id, block, blockProps, source != null ? actor : null);
                    break;
                case "applyPower": case "applyPowerAsc":
                    foreach (int id in Targets()) WireApplyPower(st, id, op.StrArg, op.IsDebuff, op.AllowNeg,
                        op.Kind == "applyPower" ? op.Amount : AscAmount(), op.IsSingle);
                    break;
                case nameof(IrKind.ApplyPowerIfPresent):
                    foreach (int id in Targets())
                        if (st.FindC(id)?.HasPower(op.StrArg) == true)
                            WireApplyPower(st, id, op.StrArg, op.IsDebuff, op.AllowNeg, op.Amount, op.IsSingle);
                    break;
                case "draw":
                    if (player != null) WireDrawCards(st, player, (int)op.Amount);
                    break;
                case nameof(IrKind.DrawIfNoAttacks):
                    if (player != null && !player.Hand.Exists(c => c.CardType == "attack"))
                        WireDrawCards(st, player, (int)op.Amount);
                    break;
                case "discardChosen": case "discardAllHand":
                    if (player != null) MoveSelected(player, source, op.Kind == "discardChosen" ? (int)op.Amount : player.Hand.Count, player.Discard);
                    break;
                case "exhaustChosen":
                    if (player != null) MoveSelected(player, source, (int)op.Amount, player.Exhaust);
                    break;
                case "addGeneratedCard":
                    for (int i = 0; i < (int)op.Amount; i++)
                    {
                        if (player != null) AddGeneratedCard(st, player, op);
                        else foreach (var p in st.Players) AddGeneratedCard(st, p, op);
                    }
                    break;
                case "gainEnergy":
                    if (player != null) GainEnergy(player, (int)op.Amount);
                    break;
                case nameof(IrKind.GainCurrentEnergy):
                    if (player != null && !st.IsEnding) GainEnergy(player, player.Energy);
                    break;
                case "gainStars":
                    if (player != null) player.Stars += (int)op.Amount;
                    break;
                case "heal":
                    foreach (int id in Targets()) Heal(st, id, op.Amount);
                    break;
                case "channelOrb":
                    if (player != null) ChannelOrb(st, player, op.StrArg);
                    break;
                case nameof(IrKind.AddOrbSlots):
                    if (player != null && !st.IsEnding)
                        player.OrbCapacity += Math.Min(10 - player.OrbCapacity, (int)op.Amount);
                    break;
                case nameof(IrKind.RemoveOrbSlots):
                    if (player != null && !st.IsEnding)
                    {
                        player.OrbCapacity = Math.Max(0, player.OrbCapacity - (int)op.Amount);
                        int excess = player.Orbs.Count - player.OrbCapacity;
                        if (excess > 0) player.Orbs.RemoveRange(player.OrbCapacity, excess);
                    }
                    break;
                case nameof(IrKind.AddPlayedCardCombatCost):
                    if (player != null && source != null && player.Play.Find(c => c.InstId == source.InstId) is { } played)
                        played.CombatCostDelta += (int)op.Amount;
                    break;
                case "forge":
                    if (player != null) Forge(st, player, op.Amount);
                    break;
                case "summonOsty":
                    if (player != null) SummonOsty(st, player, op.Amount);
                    break;
                default:
                    throw new InvalidOperationException($"Unsupported Tier-2 operation {op.Kind} for {kind} {entry}");
            }
        }
    }

    private static void MoveSelected(TPlayer player, TCard? source, int count, List<TCard> destination)
    {
        // These execution paths have no explicit choices: take the first eligible hand cards in order.
        for (int i = 0; i < player.Hand.Count && count > 0;)
        {
            var card = player.Hand[i];
            if (card.InstId == source?.InstId) { i++; continue; }
            player.Hand.RemoveAt(i);
            destination.Add(card);
            count--;
        }
    }

    private static void AddGeneratedCard(TSimState st, TPlayer p, T2Op op)
    {
        var pile = op.Target switch
        {
            "hand" => p.Hand, "draw" => p.Draw, "discard" => p.Discard, "exhaust" => p.Exhaust, "play" => p.Play,
            _ => throw new InvalidOperationException($"Unknown generated-card pile: {op.Target}")
        };
        var card = new TCard { InstId = st.NextInstanceId++, Entry = op.StrArg, CardType = op.StrArg2, Cost = op.Param1 };
        if (op.StrArg3 == "top") pile.Insert(0, card);
        else pile.Add(card);
    }

    private static void GainEnergy(TPlayer p, int amount) => p.Energy = ClampIntDelta(p.Energy, amount, StatCap);

    private static void Heal(TSimState st, int id, decimal amount)
    {
        if (st.FindC(id) is { } c) c.Hp = (int)Math.Clamp(c.Hp + amount, 0, c.MaxHp);
    }

    private static void ChannelOrb(TSimState st, TPlayer p, string kind)
    {
        if (st.IsEnding) return;
        if (p.Orbs.Count == p.OrbCapacity) EvokeOrb(st, p);
        p.Orbs.Add(DefaultOrb(st.NextInstanceId++, kind));
    }

    private static void EvokeOrb(TSimState st, TPlayer p)
    {
        if (st.IsEnding || p.Orbs.Count == 0) return;
        var orb = p.Orbs[0];
        p.Orbs.RemoveAt(0);
        switch (orb.Kind)
        {
            case "lightning": case "dark":
                TCreature? target = null;
                foreach (var enemy in st.Creatures)
                {
                    if (enemy.Side != 2 || enemy.Hp <= 0) continue;
                    if (target == null || enemy.Hp < target.Hp) target = enemy;
                    if (orb.Kind == "lightning") break;
                }
                if (target != null) TApplyDamageHit(st, p.Cid, target.Id, orb.BaseEvoke, UnpoweredDamage);
                break;
            case "frost": WireGainBlock(st, p.Cid, orb.BaseEvoke, ValuePropFlags.Unpowered); break;
            case "plasma": GainEnergy(p, Math.Max(0, (int)orb.BaseEvoke)); break;
            case "glass":
                foreach (var enemy in st.Creatures)
                    if (enemy.Side == 2 && enemy.Hp > 0) TApplyDamageHit(st, p.Cid, enemy.Id, orb.BasePassive * 2, UnpoweredDamage);
                break;
        }
    }

    private static void Forge(TSimState st, TPlayer p, decimal amount)
    {
        if (st.IsEnding) return;
        static bool IsBlade(TCard c) => c.Entry == "SOVEREIGN_BLADE" && !c.IsDupe;
        if (!p.Hand.Exists(IsBlade) && !p.Draw.Exists(IsBlade) && !p.Discard.Exists(IsBlade) && !p.Play.Exists(IsBlade))
        {
            var blade = new TCard { InstId = st.NextInstanceId++, Entry = "SOVEREIGN_BLADE", Cost = 2, BaseDamage = 10 + p.SovereignBladeBonus };
            (p.Hand.Count < 10 ? p.Hand : p.Discard).Add(blade);
        }
        void Upgrade(List<TCard> pile)
        {
            foreach (var card in pile)
                if (IsBlade(card)) card.BaseDamage += amount;
        }
        Upgrade(p.Hand);
        Upgrade(p.Draw);
        Upgrade(p.Discard);
        Upgrade(p.Play);
        Upgrade(p.Exhaust);
        p.SovereignBladeBonus += amount;
    }

    private static void SummonOsty(TSimState st, TPlayer p, decimal amount)
    {
        if (amount <= 0) return;
        int hp = (int)Math.Min(amount, StatCap);
        var osty = st.Creatures.Find(c => c.Entry == "OSTY" && c.PetOwnerId == p.Pid);
        if (osty is { Hp: > 0 })
        {
            int grown = Math.Min(hp, StatCap - osty.MaxHp);
            osty.MaxHp += grown;
            osty.Hp += grown;
            return;
        }
        if (osty == null)
        {
            osty = new TCreature { Id = st.NextInstanceId++, Entry = "OSTY", Side = 1, PetOwnerId = p.Pid, MaxHp = hp, Hp = hp };
            st.Creatures.Add(osty);
            WireApplyPower(st, osty.Id, "DIE_FOR_YOU_POWER", false, false, 1, isSingle: true);
        }
        else osty.Hp = osty.MaxHp = hp;
        if (!p.PetIds.Contains(osty.Id)) p.PetIds.Add(osty.Id);
    }
}
