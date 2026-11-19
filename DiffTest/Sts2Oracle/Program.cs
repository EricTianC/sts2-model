using System.Globalization;
using System.Numerics;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;

namespace Sts2Oracle;

// Reference C# oracle ported directly from `reference/sts2/` for bit-exact
// differential verification against the Lean 4 `Sts2Model` / `sts2sim`.

internal sealed class MegaRandomOracle
{
    private const double IncrDouble = 1.1102230246251565E-16;
    private ulong _s0, _s1, _s2, _s3;

    public ulong S0 => _s0;
    public ulong S1 => _s1;
    public ulong S2 => _s2;
    public ulong S3 => _s3;

    public MegaRandomOracle(ulong seed)
    {
        _s0 = Splitmix64(ref seed);
        _s1 = Splitmix64(ref seed);
        _s2 = Splitmix64(ref seed);
        _s3 = Splitmix64(ref seed);
    }

    private MegaRandomOracle(ulong s0, ulong s1, ulong s2, ulong s3)
    {
        _s0 = s0; _s1 = s1; _s2 = s2; _s3 = s3;
    }

    public static MegaRandomOracle FromState(ulong s0, ulong s1, ulong s2, ulong s3) =>
        new(s0, s1, s2, s3);

    public MegaRandomOracle Clone() => new(_s0, _s1, _s2, _s3);

    public static ulong Splitmix64(ref ulong x)
    {
        ulong num = (x += 11400714819323198485uL);
        num = (num ^ (num >> 30)) * 13787848793156543929uL;
        num = (num ^ (num >> 27)) * 10723151780598845931uL;
        return num ^ (num >> 31);
    }

    public ulong NextULongInner()
    {
        ulong s = _s0;
        ulong s2 = _s1;
        ulong s3 = _s2;
        ulong s4 = _s3;
        ulong result = BitOperations.RotateLeft(s2 * 5, 7) * 9;
        ulong num = s2 << 17;
        s3 ^= s;
        s4 ^= s2;
        s2 ^= s3;
        s ^= s4;
        s3 ^= num;
        s4 = BitOperations.RotateLeft(s4, 45);
        _s0 = s;
        _s1 = s2;
        _s2 = s3;
        _s3 = s4;
        return result;
    }

    public double NextDouble() => (double)(NextULongInner() >> 11) * IncrDouble;

    public int Next(int maxValue) => (int)(NextDouble() * (double)maxValue);
}

internal sealed class RngOracle
{
    private readonly MegaRandomOracle _random;
    public int Counter { get; private set; }
    public MegaRandomOracle State => _random;

    public RngOracle(ulong seed) { _random = new MegaRandomOracle(seed); Counter = 0; }
    private RngOracle(MegaRandomOracle state, int counter) { _random = state; Counter = counter; }
    public static RngOracle FromState(int counter, ulong s0, ulong s1, ulong s2, ulong s3) =>
        new(MegaRandomOracle.FromState(s0, s1, s2, s3), counter);
    public RngOracle Clone() => new(_random.Clone(), Counter);
    public ulong NextUnsignedLong() { Counter++; return _random.NextULongInner(); }
    public int NextInt(int maxExclusive) => maxExclusive <= 0 ? 0 : Math.Min(_random.Next(maxExclusive), maxExclusive - 1);
    public bool NextBool() => NextInt(2) == 0;
    public double NextDouble() { Counter++; return _random.NextDouble(); }
    public float NextFloat() => (float)NextDouble();

    public static List<T> UnstableShuffleGeneric<T>(List<T> list, RngOracle rng)
    {
        var copy = new List<T>(list);
        var rng2 = new RngOracle(rng.NextUnsignedLong());
        int num = copy.Count;
        while (num > 1)
        {
            num--;
            int num2 = rng2.NextInt(num + 1);
            (copy[num2], copy[num]) = (copy[num], copy[num2]);
        }
        return copy;
    }

    public static List<long> UnstableShuffle(List<long> list, RngOracle rng) =>
        UnstableShuffleGeneric(list, rng);
}

[Flags]
internal enum ValuePropFlags
{
    None = 0,
    Unblockable = 2,
    Unpowered = 4,
    Move = 8,
    SkipHurtAnim = 16,
    FromArrow = 32
}

internal static class ValuePropEx
{
    public static bool IsPoweredAttack(this ValuePropFlags p) =>
        p.HasFlag(ValuePropFlags.Move) && !p.HasFlag(ValuePropFlags.Unpowered);

    public static bool IsPoweredBlock(this ValuePropFlags p) =>
        p.HasFlag(ValuePropFlags.Move) && !p.HasFlag(ValuePropFlags.Unpowered);

    public static bool IsCardOrMonsterMove(this ValuePropFlags p) =>
        p.HasFlag(ValuePropFlags.Move);
}

internal sealed record DamageResultRec(
    int ReceiverId,
    int OriginalTargetId,
    ValuePropFlags Props,
    long IntendedHpLoss,
    int BlockedDamage,
    int UnblockedDamage,
    int OverkillDamage,
    bool WasBlockBroken,
    bool WasFullyBlocked,
    bool WasTargetKilled);

public static class Program
{
    private const int StatCap = 999999999;

    private static string FormatDecNormalized(decimal d)
    {
        string s = d.ToString(CultureInfo.InvariantCulture);
        if (s.Contains('.'))
        {
            s = s.TrimEnd('0').TrimEnd('.');
        }
        return s == "-0" ? "0" : s;
    }

    private static string EvalRngSeq(string seedStr, string countStr)
    {
        ulong seed = ulong.Parse(seedStr, CultureInfo.InvariantCulture);
        int count = int.Parse(countStr, CultureInfo.InvariantCulture);
        var rng = new RngOracle(seed);
        var items = new List<string>(count);
        for (int i = 0; i < count; i++)
        {
            ulong u = rng.NextUnsignedLong();
            int i100 = rng.NextInt(100);
            bool b = rng.NextBool();
            double d = rng.NextDouble();
            ulong bits = BitConverter.DoubleToUInt64Bits(d);
            items.Add($"{u},{i100},{(b ? 1 : 0)},{bits}");
        }
        return string.Join(";", items);
    }

    private static string EvalRngShuffle(string seedStr, string listStr)
    {
        ulong seed = ulong.Parse(seedStr, CultureInfo.InvariantCulture);
        var rng = new RngOracle(seed);
        var xs = string.IsNullOrWhiteSpace(listStr)
            ? new List<long>()
            : listStr.Split(',', StringSplitOptions.RemoveEmptyEntries)
                     .Select(t => long.Parse(t.Trim(), CultureInfo.InvariantCulture))
                     .ToList();
        var shuffled = RngOracle.UnstableShuffle(xs, rng);
        return string.Join(",", shuffled);
    }

    private static string EvalDmgPipe(string[] f)
    {
        decimal baseAmt = decimal.Parse(f[1], CultureInfo.InvariantCulture);
        var props = (ValuePropFlags)int.Parse(f[2], CultureInfo.InvariantCulture);
        int str = int.Parse(f[3], CultureInfo.InvariantCulture);
        bool vuln = f[4] == "1";
        bool phrog = f[5] == "1";
        bool weak = f[6] == "1";
        int lateMulS2 = int.Parse(f[7], CultureInfo.InvariantCulture);
        int capVal = int.Parse(f[8], CultureInfo.InvariantCulture);

        decimal num = baseAmt;
        // Additive
        if (str != 0 && props.IsPoweredAttack())
        {
            num += str;
        }
        // Multiplicative: Dealer powers (Weak) then Target powers (Vulnerable)
        if (weak && props.IsPoweredAttack())
        {
            num *= 0.75m;
        }
        if (vuln && props.IsPoweredAttack())
        {
            num *= phrog ? 1.75m : 1.5m;
        }
        // MultiplicativeLate
        if (lateMulS2 != 100 && props.IsPoweredAttack())
        {
            num *= (decimal)lateMulS2 / 100m;
        }
        // Cap
        decimal minCap = decimal.MaxValue;
        if (capVal >= 0)
        {
            decimal cap = capVal;
            if (cap < minCap)
            {
                if (cap < num) num = cap;
                minCap = cap;
            }
        }
        num = Math.Max(0m, num);
        return $"{(long)decimal.Truncate(num)}|{FormatDecNormalized(num)}";
    }

    private static string EvalBlkPipe(string[] f)
    {
        decimal baseAmt = decimal.Parse(f[1], CultureInfo.InvariantCulture);
        var props = (ValuePropFlags)int.Parse(f[2], CultureInfo.InvariantCulture);
        int dex = int.Parse(f[3], CultureInfo.InvariantCulture);
        bool frail = f[4] == "1";

        decimal num = baseAmt;
        if (dex != 0 && props.IsPoweredBlock())
        {
            num += dex;
        }
        if (frail && props.IsPoweredBlock())
        {
            num *= 0.75m;
        }
        num = Math.Max(0m, num);
        return $"{(long)decimal.Truncate(num)}|{FormatDecNormalized(num)}";
    }

    private static (int hp, int blk, DamageResultRec res) LoseHpInternal(int id, int hp, int blk, decimal amount, ValuePropFlags props)
    {
        bool killed = hp > 0 && amount >= hp;
        decimal clamped = Math.Clamp(amount, 0m, (decimal)StatCap);
        int hpLoss = Math.Max(0, (int)decimal.Truncate(clamped));
        int prevHp = hp;
        int newHp = prevHp - Math.Min(prevHp, hpLoss);
        int unblocked = prevHp - newHp;
        int overkill = killed ? (hpLoss - Math.Min(hpLoss, prevHp)) : 0;
        var res = new DamageResultRec(id, id, props, 0, 0, unblocked, overkill, false, false, killed);
        return (newHp, blk, res);
    }

    private static string EvalCreatureDmg(string[] f)
    {
        int tHp = int.Parse(f[1], CultureInfo.InvariantCulture);
        int tBlk = int.Parse(f[2], CultureInfo.InvariantCulture);
        int ostyHp = int.Parse(f[3], CultureInfo.InvariantCulture);
        var props = (ValuePropFlags)int.Parse(f[4], CultureInfo.InvariantCulture);
        decimal rawDmg = decimal.Parse(f[5], CultureInfo.InvariantCulture);
        bool intang = f[6] == "1";

        // ModifyDamageInternal: Intangible ModifyDamageCap = 1m when target is target(100)
        decimal modifiedAmt = rawDmg;
        if (intang)
        {
            decimal minCap = decimal.MaxValue;
            if (1m < minCap && 1m < modifiedAmt)
            {
                modifiedAmt = 1m;
            }
        }
        modifiedAmt = Math.Max(0m, modifiedAmt);

        // Block absorption (on Target 100)
        decimal blockedDec = 0m;
        bool blkBroken = false;
        bool fullyBlocked = false;
        if (tHp > 0) // target is alive
        {
            bool hadBlock = tBlk > 0;
            blockedDec = props.HasFlag(ValuePropFlags.Unblockable) ? 0m : Math.Min((decimal)tBlk, modifiedAmt);
            int blockedTrunc = Math.Max(0, (int)decimal.Truncate(blockedDec));
            tBlk = tBlk - Math.Min(tBlk, blockedTrunc);
            blkBroken = tBlk == 0 && blockedDec > 0m;
            decimal remAfter = Math.Max(0m, modifiedAmt - blockedDec);
            fullyBlocked = !props.HasFlag(ValuePropFlags.Unblockable) && (blockedDec > 0m || hadBlock) && (long)decimal.Truncate(remAfter) == 0;
        }
        else
        {
            // Target already dead -> CreatureCmd.Damage returns early!
            return $"{tHp},{tBlk},{ostyHp},0,0,0,0,0";
        }

        decimal dmgRemaining = Math.Max(0m, modifiedAmt - blockedDec);
        // BeforeOsty: no modifier here in harness
        decimal unblockedAmt0 = dmgRemaining;

        // Unblocked target redirection (Osty DieForYou: Osty alive & IsPoweredAttack)
        int ubTargetId = (ostyHp > 0 && props.IsPoweredAttack()) ? 101 : 100;

        var results = new List<DamageResultRec>();
        int overkill = 0;
        if (ubTargetId == 100)
        {
            decimal ubAmt = unblockedAmt0;
            if (intang && ubAmt >= 1m) ubAmt = 1m;
            var (newTHp, _, resU) = LoseHpInternal(100, tHp, tBlk, ubAmt, props);
            tHp = newTHp;
            overkill = resU.OverkillDamage;
            results.Add(resU with
            {
                IntendedHpLoss = (long)decimal.Truncate(dmgRemaining),
                OriginalTargetId = 100,
                BlockedDamage = Math.Max(0, (int)decimal.Truncate(blockedDec)),
                WasBlockBroken = blkBroken,
                WasFullyBlocked = fullyBlocked
            });
        }
        else
        {
            // Osty (101) takes unblocked damage without Intangible
            var (newOstyHp, _, resU) = LoseHpInternal(101, ostyHp, 0, unblockedAmt0, props);
            ostyHp = newOstyHp;
            overkill = resU.OverkillDamage;
            results.Add(resU with
            {
                IntendedHpLoss = (long)decimal.Truncate(dmgRemaining),
                OriginalTargetId = 100
            });
            // Overkill spill-over onto originalTarget (100) with AfterOsty
            decimal origAmt = overkill;
            if (intang && origAmt >= 1m) origAmt = 1m;
            if (origAmt > 0m)
            {
                var (newTHp, _, resO) = LoseHpInternal(100, tHp, tBlk, origAmt, props);
                tHp = newTHp;
                results.Add(resO with
                {
                    IntendedHpLoss = overkill,
                    OriginalTargetId = 100,
                    BlockedDamage = Math.Max(0, (int)decimal.Truncate(blockedDec)),
                    WasBlockBroken = blkBroken,
                    WasFullyBlocked = fullyBlocked
                });
            }
            else
            {
                results.Add(new DamageResultRec(
                    100, 100, props, 0,
                    Math.Max(0, (int)decimal.Truncate(blockedDec)),
                    0, 0, blkBroken, fullyBlocked, false));
            }
        }

        int totalUnblk = results.Sum(r => r.UnblockedDamage);
        int totalBlk = results.Sum(r => r.BlockedDamage);
        int totalOver = results.Sum(r => r.OverkillDamage);
        int tKilled = results.Any(r => r.ReceiverId == 100 && r.WasTargetKilled) ? 1 : 0;
        int oKilled = results.Any(r => r.ReceiverId == 101 && r.WasTargetKilled) ? 1 : 0;
        return $"{tHp},{tBlk},{ostyHp},{totalUnblk},{totalBlk},{totalOver},{tKilled},{oKilled}";
    }

    private static int ClampPowerAmount(int a) => Math.Clamp(a, -999999999, 999999999);

    private static bool ShouldRemovePower(int amt, bool allowNeg) => allowNeg ? amt == 0 : amt <= 0;

    private static int GetPowerTypeForAmount(bool isDebuff, int amt, bool isSingle, bool allowNeg)
    {
        // 0=Buff, 1=Debuff (PowerModel.GetTypeForAmount)
        if (!isSingle && allowNeg && amt < 0) return 1;
        if (!allowNeg && isDebuff && amt < 0) return 0;
        return isDebuff ? 1 : 0;
    }

    private static string EvalPowerStack(string[] f)
    {
        int existAmt = int.Parse(f[1], CultureInfo.InvariantCulture);
        decimal applyAmt = decimal.Parse(f[2], CultureInfo.InvariantCulture);
        bool isSingle = f[3] == "1";
        bool allowNeg = f[4] == "1";
        int artAmt = int.Parse(f[5], CultureInfo.InvariantCulture);
        bool isDebuff = f[6] == "1";

        if (applyAmt == 0m)
        {
            int curAmt = existAmt;
            int rem0 = existAmt == 0 ? 1 : 0;
            return $"{curAmt},{rem0},{artAmt}";
        }

        decimal amtAfterRecv = applyAmt;
        // Artifact check (ModifyPowerAmountReceived) on visible power
        int typeForAmt = GetPowerTypeForAmount(isDebuff, (int)decimal.Truncate(amtAfterRecv), isSingle, allowNeg);
        if (typeForAmt == 1 && artAmt > 0)
        {
            amtAfterRecv = 0m;
            artAmt = ClampPowerAmount(artAmt - 1);
        }

        if (existAmt != 0)
        {
            int delta = isSingle ? 0 : (int)decimal.Truncate(amtAfterRecv);
            int newAmt = ClampPowerAmount(existAmt + delta);
            bool removed = ShouldRemovePower(newAmt, allowNeg);
            return $"{(removed ? 0 : newAmt)},{(removed ? 1 : 0)},{artAmt}";
        }
        else
        {
            int rawInt = isSingle
                ? ((long)decimal.Truncate(amtAfterRecv) == 0 ? 0 : 1)
                : (int)decimal.Truncate(amtAfterRecv);
            int clamped = ClampPowerAmount(rawInt);
            bool removed = ShouldRemovePower(clamped, allowNeg);
            return $"{(removed ? 0 : clamped)},{(removed ? 1 : 0)},{artAmt}";
        }
    }

    private static string EvalCardCost(string[] f)
    {
        int baseCost = int.Parse(f[1], CultureInfo.InvariantCulture);
        bool costsX = f[2] == "1";
        int energy = int.Parse(f[3], CultureInfo.InvariantCulture);
        int stars = int.Parse(f[4], CultureInfo.InvariantCulture);
        int starCost = int.Parse(f[5], CultureInfo.InvariantCulture);
        int modType = int.Parse(f[6], CultureInfo.InvariantCulture);
        int modAmt = int.Parse(f[7], CultureInfo.InvariantCulture);
        bool excessStars = f[8] == "1";
        int hookDelta = int.Parse(f[9], CultureInfo.InvariantCulture);

        int eff;
        if (costsX)
        {
            eff = energy;
        }
        else if (baseCost < 0)
        {
            eff = baseCost;
        }
        else
        {
            int afterLocal = modType switch
            {
                1 => modAmt,
                2 => baseCost + modAmt,
                _ => baseCost
            };
            // Hook.ModifyEnergyCostInCombat returns originalCost early when < 0m (Hook.cs:1626)
            decimal afterGlobalDec = afterLocal < 0 ? (decimal)afterLocal : (decimal)afterLocal + (decimal)hookDelta;
            int afterGlobal = (int)decimal.Truncate(afterGlobalDec);
            eff = Math.Max(0, afterGlobal);
        }

        int e0 = Math.Max(0, eff);
        int s0 = Math.Max(0, starCost);
        int eReq, sReq;
        if (e0 > energy && excessStars)
        {
            eReq = energy;
            sReq = s0 + (e0 - energy) * 2;
        }
        else
        {
            eReq = e0;
            sReq = s0;
        }
        bool canPay = !(eReq > energy) && !(sReq > stars);
        return $"{eff},{(canPay ? 1 : 0)},{eReq},{sReq}";
    }

    private static string EvalRarityOdds(string[] f)
    {
        ulong seed = ulong.Parse(f[1], CultureInfo.InvariantCulture);
        bool scarcity = f[2] == "1";
        int typeCode = int.Parse(f[3], CultureInfo.InvariantCulture);
        int numRolls = int.Parse(f[4], CultureInfo.InvariantCulture);

        var rng = new RngOracle(seed);
        float currentValue = -0.05f;
        float growth = scarcity ? 0.005f : 0.01f;
        float baseRare = typeCode switch
        {
            0 => scarcity ? 0.0149f : 0.03f,
            1 => scarcity ? 0.05f : 0.1f,
            2 => 1.0f,
            3 => scarcity ? 0.045f : 0.09f,
            4 => 0.33f,
            5 => 0.1f,
            _ => 0.05f
        };
        float baseUnc = typeCode switch
        {
            0 => 0.37f,
            1 => 0.4f,
            2 => 0.0f,
            3 => 0.37f,
            4 => 0.33f,
            5 => 0.5f,
            _ => 0.4f
        };

        var sb = new StringBuilder(numRolls);
        for (int i = 0; i < numRolls; i++)
        {
            float effOffset = typeCode == 2 ? 0.0f : currentValue;
            float num = rng.NextFloat();
            float rareThresh = baseRare + effOffset;
            float uncThresh = baseUnc + rareThresh;
            char rarChar;
            if (num < rareThresh)
            {
                rarChar = 'R';
                currentValue = -0.05f;
            }
            else if (num < uncThresh)
            {
                rarChar = 'U';
                currentValue = Math.Min(currentValue + growth, 0.4f);
            }
            else
            {
                rarChar = 'C';
                currentValue = Math.Min(currentValue + growth, 0.4f);
            }
            sb.Append(rarChar);
        }
        uint finalBits = BitConverter.SingleToUInt32Bits(currentValue);
        return $"{sb}|{finalBits}";
    }

    private static string EvalModSort(string[] f)
    {
        string raw = f.Length > 1 ? f[1] : "";
        var list = new List<string>();
        if (!string.IsNullOrWhiteSpace(raw))
        {
            foreach (string part in raw.Split(','))
            {
                string id = part.Trim();
                if (list.Contains(id)) continue;
                int insertAt = list.Count;
                for (int i = 0; i < list.Count; i++)
                {
                    if (string.Compare(id, list[i], StringComparison.Ordinal) < 0)
                    {
                        insertAt = i;
                        break;
                    }
                }
                list.Insert(insertAt, id);
            }
        }
        return string.Join(",", list);
    }

    // ========================================================================
    // 10. QUEUE_SET (`ActionQueueSet.cs`)
    // ========================================================================
    private enum QActionState { None, WaitingForExecution, Executing, GatheringPlayerChoice, ReadyToResumeExecuting, Finished, Canceled }
    private enum QActionType { None, Combat, CombatPlayPhaseOnly, NonCombat, Any }

    private sealed class QAction
    {
        public int ActionId;
        public int OwnerId;
        public QActionType ActionType;
        public bool IsPlayerDriven;
        public bool IsPlayCard;
        public QActionState State;
    }

    private sealed class PlayerQ
    {
        public int OwnerId;
        public List<QAction> Actions = new();
        public int? CancellingPlayCardActionId;
        public bool IsCancellingPlayerDrivenCombatActions;
        public bool IsCancellingCombatActions = true;
        public bool IsPaused;
    }

    private static bool IsQActionEligible(bool isInCombat, bool qPaused, QAction a)
    {
        if (a.State == QActionState.Canceled) return false;
        if (isInCombat && a.ActionType == QActionType.NonCombat) return false;
        if (!isInCombat && (a.ActionType == QActionType.Combat || a.ActionType == QActionType.CombatPlayPhaseOnly)) return false;
        if (qPaused && a.ActionType == QActionType.CombatPlayPhaseOnly) return false;
        if (a.State == QActionState.GatheringPlayerChoice) return false;
        return a.State == QActionState.WaitingForExecution || a.State == QActionState.ReadyToResumeExecuting;
    }

    private static string EvalQueueSet(string[] f)
    {
        var pids = f[1].Split(',', StringSplitOptions.RemoveEmptyEntries)
                       .Select(s => int.Parse(s.Trim(), CultureInfo.InvariantCulture))
                       .ToList();
        string opsRaw = f.Length > 2 ? f[2] : "";
        var ops = string.IsNullOrWhiteSpace(opsRaw)
            ? Array.Empty<string>()
            : opsRaw.Split(';');

        var queues = pids.Select(pid => new PlayerQ { OwnerId = pid, IsCancellingCombatActions = false }).ToList();
        var waiting = new List<(int oldId, int newId)>();
        int nextActionId = 0;
        bool isInCombat = true;
        int canceledCount = 0;
        var picked = new List<int>();

        foreach (string rawOp in ops)
        {
            string tok = rawOp.Trim();
            if (tok.Length == 0) continue;
            string[] p = tok.Split(',');
            switch (p[0])
            {
                case "ENQ":
                {
                    int pid = int.Parse(p[1], CultureInfo.InvariantCulture);
                    int tc = int.Parse(p[2], CultureInfo.InvariantCulture);
                    bool pDriven = p[3] == "1";
                    bool isPlay = p[4] == "1";
                    var atp = tc switch { 0 => QActionType.None, 1 => QActionType.Combat, 2 => QActionType.CombatPlayPhaseOnly, 3 => QActionType.NonCombat, _ => QActionType.Any };
                    int assignedId = nextActionId++;
                    var q = queues.FirstOrDefault(x => x.OwnerId == pid);
                    if (q != null)
                    {
                        bool cancelForChoice = q.CancellingPlayCardActionId.HasValue && isPlay;
                        bool cancelForEndTurn = q.IsCancellingPlayerDrivenCombatActions && pDriven && atp != QActionType.NonCombat && atp != QActionType.Any;
                        bool cancelForCombatEnd = q.IsCancellingCombatActions && (atp == QActionType.Combat || atp == QActionType.CombatPlayPhaseOnly);
                        if (cancelForChoice || cancelForEndTurn || cancelForCombatEnd)
                        {
                            canceledCount++;
                        }
                        else
                        {
                            q.Actions.Add(new QAction
                            {
                                ActionId = assignedId,
                                OwnerId = pid,
                                ActionType = atp,
                                IsPlayerDriven = pDriven,
                                IsPlayCard = isPlay,
                                State = QActionState.WaitingForExecution
                            });
                        }
                    }
                    break;
                }
                case "PICK":
                {
                    QAction? best = null;
                    foreach (var q in queues)
                    {
                        while (q.Actions.Count > 0 && q.Actions[0].State == QActionState.Canceled)
                            q.Actions.RemoveAt(0);
                        if (q.Actions.Count == 0) continue;
                        var hd = q.Actions[0];
                        if (!IsQActionEligible(isInCombat, q.IsPaused, hd)) continue;
                        if (best == null || hd.ActionId < best.ActionId) best = hd;
                    }
                    picked.Add(best?.ActionId ?? -1);
                    break;
                }
                case "EXEC":
                {
                    int aid = int.Parse(p[1], CultureInfo.InvariantCulture);
                    foreach (var q in queues)
                    {
                        if (q.Actions.Count > 0 && q.Actions[0].ActionId == aid)
                            q.Actions[0].State = QActionState.Executing;
                    }
                    break;
                }
                case "PAUSE":
                {
                    int aid = int.Parse(p[1], CultureInfo.InvariantCulture);
                    bool cpc = p[2] == "1";
                    var targetQ = queues.FirstOrDefault(q => q.Actions.Count > 0 && q.Actions[0].ActionId == aid);
                    if (targetQ != null)
                    {
                        (int oldId, int newId)? early = null;
                        int wIdx = waiting.FindIndex(w => w.oldId == aid);
                        if (wIdx >= 0)
                        {
                            early = waiting[wIdx];
                            waiting.RemoveAt(wIdx);
                        }
                        int? maxId = early?.newId;
                        var head = targetQ.Actions[0];
                        head.State = QActionState.GatheringPlayerChoice;
                        if (cpc)
                        {
                            for (int i = 1; i < targetQ.Actions.Count; i++)
                            {
                                var a = targetQ.Actions[i];
                                if (a.IsPlayCard && a.State == QActionState.WaitingForExecution && (!maxId.HasValue || a.ActionId < maxId.Value))
                                {
                                    targetQ.Actions.RemoveAt(i);
                                    canceledCount++;
                                    i--;
                                }
                            }
                            targetQ.CancellingPlayCardActionId = aid;
                        }
                        if (early.HasValue)
                        {
                            head.ActionId = early.Value.newId;
                            head.State = QActionState.ReadyToResumeExecuting;
                            targetQ.CancellingPlayCardActionId = null;
                        }
                    }
                    break;
                }
                case "RESUME":
                {
                    int oldId = int.Parse(p[1], CultureInfo.InvariantCulture);
                    int newId = nextActionId++;
                    bool found = false;
                    foreach (var q in queues)
                    {
                        bool anyHere = q.Actions.Any(a => a.ActionId == oldId && a.State == QActionState.GatheringPlayerChoice);
                        if (anyHere)
                        {
                            found = true;
                            q.CancellingPlayCardActionId = null;
                            foreach (var a in q.Actions)
                            {
                                if (a.ActionId == oldId && a.State == QActionState.GatheringPlayerChoice)
                                {
                                    a.ActionId = newId;
                                    a.State = QActionState.ReadyToResumeExecuting;
                                }
                            }
                        }
                    }
                    if (!found) waiting.Add((oldId, newId));
                    break;
                }
                case "POP":
                {
                    int aid = int.Parse(p[1], CultureInfo.InvariantCulture);
                    foreach (var q in queues)
                    {
                        if (q.Actions.Count > 0 && q.Actions[0].ActionId == aid)
                        {
                            q.Actions.RemoveAt(0);
                            if (q.CancellingPlayCardActionId == aid) q.CancellingPlayCardActionId = null;
                        }
                    }
                    break;
                }
                case "CANCELPD":
                {
                    foreach (var q in queues)
                    {
                        q.IsCancellingPlayerDrivenCombatActions = true;
                        for (int i = 0; i < q.Actions.Count; i++)
                        {
                            var a = q.Actions[i];
                            if (a.IsPlayerDriven && a.ActionType != QActionType.NonCombat && a.ActionType != QActionType.Any && a.State == QActionState.WaitingForExecution)
                            {
                                q.Actions.RemoveAt(i);
                                canceledCount++;
                                i--;
                            }
                        }
                    }
                    break;
                }
                case "CEND":
                {
                    isInCombat = false;
                    foreach (var q in queues)
                    {
                        for (int i = 0; i < q.Actions.Count; i++)
                        {
                            var a = q.Actions[i];
                            if ((a.ActionType == QActionType.Combat || a.ActionType == QActionType.CombatPlayPhaseOnly) && a.State != QActionState.Executing)
                            {
                                q.Actions.RemoveAt(i);
                                canceledCount++;
                                i--;
                            }
                        }
                        q.CancellingPlayCardActionId = null;
                        q.IsCancellingPlayerDrivenCombatActions = false;
                        q.IsCancellingCombatActions = true;
                    }
                    break;
                }
                case "CSTART":
                {
                    isInCombat = true;
                    foreach (var q in queues) q.IsCancellingCombatActions = false;
                    break;
                }
                case "PPAUSED":
                {
                    bool flg = p[1] == "1";
                    foreach (var q in queues)
                    {
                        q.IsPaused = flg;
                        q.IsCancellingPlayerDrivenCombatActions = false;
                    }
                    break;
                }
            }
        }
        return $"{nextActionId}|{string.Join(",", picked)}|{canceledCount}|{string.Join(",", queues.Select(q => q.Actions.Count))}";
    }

    // ========================================================================
    // 11. TIMELINE_SEEK (Multi-player combat replay, keyframe seek & FNV-1a checksum)
    // ========================================================================
    private const ulong FnvOffsetBasis = 14695981039346656037uL;
    private const ulong FnvPrime = 1099511628211uL;
    private static ulong Fnv1aByte(ulong h, byte b) => (h ^ b) * FnvPrime;
    private static ulong Fnv1aUInt64(ulong h, ulong v)
    {
        for (int i = 0; i < 8; i++) h = Fnv1aByte(h, (byte)((v >> (8 * i)) & 0xFF));
        return h;
    }
    private static ulong Fnv1aNat(ulong h, int n) => Fnv1aUInt64(h, (ulong)n);
    private static ulong Fnv1aInt(ulong h, long x) => Fnv1aNat(Fnv1aByte(h, (byte)(x < 0 ? 1 : 0)), (int)Math.Abs(x));
    private static ulong Fnv1aString(ulong h, string s)
    {
        h = Fnv1aUInt64(h, (ulong)s.Length);
        foreach (char c in s) h = Fnv1aByte(h, (byte)((uint)c % 256u));
        return h;
    }

    private sealed class TPower
    {
        public int InstId; public string Entry = ""; public bool IsDebuff; public bool AllowNeg; public int Amt;
        public TPower Clone() => new() { InstId = InstId, Entry = Entry, IsDebuff = IsDebuff, AllowNeg = AllowNeg, Amt = Amt };
    }
    private sealed class TCreature
    {
        public int Id; public string Entry = ""; public int Side; public int Hp; public int MaxHp; public int Block;
        public List<TPower> Powers = new();
        public string MoveId = ""; public List<string> StateLog = new();
        public TCreature Clone() => new() { Id = Id, Entry = Entry, Side = Side, Hp = Hp, MaxHp = MaxHp, Block = Block, Powers = Powers.Select(p => p.Clone()).ToList(), MoveId = MoveId, StateLog = new List<string>(StateLog) };
        public int GetPowerAmt(string entry) => Powers.FirstOrDefault(p => p.Entry == entry)?.Amt ?? 0;
        public bool HasPower(string entry) => Powers.Any(p => p.Entry == entry);
    }
    private sealed class TCard
    {
        public int InstId; public string Entry = ""; public string CardType = "attack"; public int Cost; public int UpgradeLevel;
        public int BaseDamage; public int BaseBlock; public bool GainsBlock;
        public TCard Clone() => new() { InstId = InstId, Entry = Entry, CardType = CardType, Cost = Cost, UpgradeLevel = UpgradeLevel, BaseDamage = BaseDamage, BaseBlock = BaseBlock, GainsBlock = GainsBlock };
    }
    private sealed class TPlayer
    {
        public int Pid; public int Cid; public int Energy; public int BaseMaxEnergy; public int Stars; public int TurnNumber;
        public List<string?> Potions = new();
        public List<string> Relics = new();
        public List<TCard> Hand = new(); public List<TCard> Draw = new(); public List<TCard> Discard = new(); public List<TCard> Exhaust = new();
        public TPlayer Clone() => new() { Pid = Pid, Cid = Cid, Energy = Energy, BaseMaxEnergy = BaseMaxEnergy, Stars = Stars, TurnNumber = TurnNumber, Potions = new List<string?>(Potions), Relics = new List<string>(Relics), Hand = Hand.Select(c => c.Clone()).ToList(), Draw = Draw.Select(c => c.Clone()).ToList(), Discard = Discard.Select(c => c.Clone()).ToList(), Exhaust = Exhaust.Select(c => c.Clone()).ToList() };
    }
    private sealed class TSimState
    {
        public ulong RunSeed = 0; public int ActIndex = 0; public int Gold = 99; public int TotalFloors = 0;
        public int CombatId = 1; public int RoundNumber = 1; public int Side = 1; public bool IsInProgress = true; public bool IsEnding = false;
        public bool HasCombat = true;
        public RngOracle Rng = new(1);
        public int NextInstanceId = 1000;
        public int NextActionId = 0; public int NextHookId = 0; public bool IsInCombat = true; public int CanceledCount = 0; public int NextChecksumId = 0;
        public List<TCreature> Creatures = new();
        public List<TPlayer> Players = new();
        public TSimState Clone() => new() { RunSeed = RunSeed, ActIndex = ActIndex, Gold = Gold, TotalFloors = TotalFloors, CombatId = CombatId, RoundNumber = RoundNumber, Side = Side, IsInProgress = IsInProgress, IsEnding = IsEnding, HasCombat = HasCombat, Rng = Rng.Clone(), NextInstanceId = NextInstanceId, NextActionId = NextActionId, NextHookId = NextHookId, IsInCombat = IsInCombat, CanceledCount = CanceledCount, NextChecksumId = NextChecksumId, Creatures = Creatures.Select(c => c.Clone()).ToList(), Players = Players.Select(p => p.Clone()).ToList() };
        public TCreature? FindC(int id) => Creatures.FirstOrDefault(c => c.Id == id);
        public TPlayer? FindP(int pid) => Players.FirstOrDefault(p => p.Pid == pid);
    }

    private static ulong ComputeTimelineChecksum(TSimState st)
    {
        ulong h = FnvOffsetBasis;
        h = Fnv1aUInt64(h, st.RunSeed);
        h = Fnv1aNat(h, st.ActIndex);
        h = Fnv1aNat(h, st.Gold);
        h = Fnv1aNat(h, st.TotalFloors);
        h = Fnv1aNat(h, st.NextActionId);
        h = Fnv1aNat(h, st.NextHookId);
        h = Fnv1aByte(h, (byte)(st.IsInCombat ? 1 : 0));
        h = Fnv1aNat(h, st.CanceledCount);
        h = Fnv1aNat(h, st.NextChecksumId);
        if (!st.HasCombat)
            return Fnv1aByte(h, 0);
        h = Fnv1aByte(h, 1);
        h = Fnv1aNat(h, st.CombatId);
        h = Fnv1aNat(h, st.RoundNumber);
        h = Fnv1aNat(h, st.Side);
        h = Fnv1aByte(h, (byte)(st.IsInProgress ? 1 : 0));
        h = Fnv1aByte(h, (byte)(st.IsEnding ? 1 : 0));
        h = Fnv1aNat(h, st.Rng.Counter);
        h = Fnv1aUInt64(h, st.Rng.State.S0);
        h = Fnv1aUInt64(h, st.Rng.State.S1);
        h = Fnv1aUInt64(h, st.Rng.State.S2);
        h = Fnv1aUInt64(h, st.Rng.State.S3);
        h = Fnv1aNat(h, st.NextInstanceId);
        h = Fnv1aNat(h, st.Creatures.Count);
        foreach (var c in st.Creatures)
        {
            h = Fnv1aNat(h, c.Id);
            h = Fnv1aNat(h, c.Hp);
            h = Fnv1aNat(h, c.MaxHp);
            h = Fnv1aNat(h, c.Block);
            h = Fnv1aNat(h, c.Powers.Count);
            foreach (var p in c.Powers)
            {
                h = Fnv1aString(h, p.Entry);
                h = Fnv1aInt(h, p.Amt);
            }
        }
        h = Fnv1aNat(h, st.Players.Count);
        foreach (var p in st.Players)
        {
            h = Fnv1aNat(h, p.Pid);
            h = Fnv1aNat(h, p.Potions.Count);
            h = Fnv1aByte(h, 1);
            h = Fnv1aNat(h, p.Energy);
            h = Fnv1aNat(h, p.Stars);
            h = Fnv1aNat(h, p.Hand.Count);
            h = Fnv1aNat(h, p.Draw.Count);
            h = Fnv1aNat(h, p.Discard.Count);
            h = Fnv1aNat(h, p.Exhaust.Count);
            foreach (var c in p.Hand.Concat(p.Draw).Concat(p.Discard))
            {
                h = Fnv1aNat(h, c.InstId);
                h = Fnv1aString(h, c.Entry);
            }
        }
        return h;
    }

    private static void TApplyDamageHit(TSimState st, int? dealerCid, int targetCid, decimal baseAmt, ValuePropFlags props)
    {
        var d = dealerCid.HasValue ? st.FindC(dealerCid.Value) : null;
        if (d != null && d.Hp <= 0) return;
        var t = st.FindC(targetCid);
        if (t == null || t.Hp <= 0) return;
        decimal num = baseAmt;
        if (props.IsPoweredAttack())
        {
            if (d != null) num += d.GetPowerAmt("STRENGTH_POWER");
            if (d != null && d.HasPower("WEAK_POWER")) num *= 0.75m;
            if (t.HasPower("VULNERABLE_POWER")) num *= 1.5m;
        }
        num = Math.Max(0m, num);
        decimal blockedDec = props.HasFlag(ValuePropFlags.Unblockable) ? 0m : Math.Min((decimal)t.Block, num);
        int blockedTrunc = Math.Max(0, (int)decimal.Truncate(blockedDec));
        t.Block -= Math.Min(t.Block, blockedTrunc);
        decimal rem = Math.Max(0m, num - blockedDec);
        int hpLoss = Math.Max(0, (int)decimal.Truncate(Math.Clamp(rem, 0m, (decimal)StatCap)));
        t.Hp -= Math.Min(t.Hp, hpLoss);
    }

    private static void TApplyPower(TSimState st, int targetCid, string entry, bool isDebuff, bool allowNeg, int amt)
    {
        if (st.IsEnding || amt == 0) return;
        var t = st.FindC(targetCid);
        if (t == null) return;
        var ex = t.Powers.FirstOrDefault(p => p.Entry == entry);
        if (ex != null)
        {
            ex.Amt = Math.Clamp(ex.Amt + amt, -StatCap, StatCap);
            bool rem = allowNeg ? ex.Amt == 0 : ex.Amt <= 0;
            if (rem) t.Powers.Remove(ex);
        }
        else
        {
            int newId = st.NextInstanceId++;
            int clamped = Math.Clamp(amt, -StatCap, StatCap);
            bool rem = allowNeg ? clamped == 0 : clamped <= 0;
            if (!rem) t.Powers.Add(new TPower { InstId = newId, Entry = entry, IsDebuff = isDebuff, AllowNeg = allowNeg, Amt = clamped });
        }
    }

    private static void TCheckWin(TSimState st)
    {
        if (!st.IsInProgress) return;
        if (st.Players.All(p => (st.FindC(p.Cid)?.Hp ?? 0) <= 0))
        {
            st.IsInProgress = false; st.IsEnding = true; return;
        }
        if (!st.Creatures.Any(c => c.Side == 2 && c.Hp > 0))
        {
            st.IsInProgress = false; st.IsEnding = true;
        }
    }

    private static void TStep(TSimState st, string tok)
    {
        void PlayCard(int pid, int cid, int? tid)
        {
            st.NextActionId++;
            var p = st.FindP(pid);
            if (p == null) return;
            var card = p.Hand.FirstOrDefault(c => c.InstId == cid);
            if (card == null || p.Energy < card.Cost) return;
            p.Energy -= card.Cost;
            p.Hand.Remove(card);
            if (card.Entry == "BASH")
            {
                if (tid.HasValue) TApplyDamageHit(st, p.Cid, tid.Value, 8m, ValuePropFlags.Move);
                if (tid.HasValue) TApplyPower(st, tid.Value, "VULNERABLE_POWER", true, false, 2);
            }
            else if (card.Entry == "STRIKE_IRONCLAD")
            {
                decimal d = card.UpgradeLevel > 0 ? 9m : 6m;
                if (tid.HasValue) TApplyDamageHit(st, p.Cid, tid.Value, d, ValuePropFlags.Move);
            }
            else if (card.Entry == "TWIN_STRIKE")
            {
                if (tid.HasValue) TApplyDamageHit(st, p.Cid, tid.Value, 5m, ValuePropFlags.Move);
                if (tid.HasValue) TApplyDamageHit(st, p.Cid, tid.Value, 5m, ValuePropFlags.Move);
            }
            else if (card.Entry == "DEFEND_IRONCLAD")
            {
                var selfC = st.FindC(p.Cid);
                if (selfC != null && !st.IsEnding && selfC.Hp > 0)
                    selfC.Block = Math.Min(StatCap, selfC.Block + 5);
            }
            else if (card.Entry == "UPPERCUT")
            {
                if (tid.HasValue) TApplyDamageHit(st, p.Cid, tid.Value, 13m, ValuePropFlags.Move);
                if (tid.HasValue) TApplyPower(st, tid.Value, "WEAK_POWER", true, false, 1);
                if (tid.HasValue) TApplyPower(st, tid.Value, "VULNERABLE_POWER", true, false, 1);
            }
            p.Discard.Add(card);
            TCheckWin(st);
        }

        void UseFirePot()
        {
            st.NextActionId++;
            var p = st.FindP(1);
            if (p == null || !st.IsInProgress || p.Potions.Count == 0 || p.Potions[0] == null) return;
            p.Potions[0] = null;
            TApplyDamageHit(st, p.Cid, 200, 20m, ValuePropFlags.Move | ValuePropFlags.Unpowered);
            TCheckWin(st);
        }

        void EndRound()
        {
            if (!st.IsInProgress) return;
            // EndPlayerTurnPhase1+2 flush hand -> discard
            foreach (var p in st.Players)
            {
                foreach (var c in p.Hand.ToList())
                {
                    p.Hand.Remove(c);
                    p.Discard.Add(c);
                }
            }
            st.Side = 2; // enemy
            // ClearTurnStartBlock(.enemy)
            foreach (var c in st.Creatures.Where(x => x.Side == 2)) c.Block = 0;
            // COOP_GUARDIAN turn
            var g = st.FindC(200);
            if (g != null && g.Hp > 0 && st.IsInProgress)
            {
                bool first = g.StateLog.Count == 0;
                string move = first ? g.MoveId : (g.MoveId == "SLAM" ? "FORTIFY" : "SLAM");
                g.MoveId = move;
                g.StateLog.Add(move);
                if (move == "SLAM")
                {
                    foreach (var ally in st.Creatures.Where(c => c.Side == 1 && c.Hp > 0))
                        TApplyDamageHit(st, g.Id, ally.Id, 7m, ValuePropFlags.Move);
                }
                else
                {
                    if (!st.IsEnding && g.Hp > 0) g.Block = Math.Min(StatCap, g.Block + 8);
                    TApplyPower(st, g.Id, "STRENGTH_POWER", false, true, 1);
                }
            }
            TCheckWin(st);
            if (!st.IsInProgress) return;
            // EndEnemyTurn
            foreach (var p in st.Players) p.TurnNumber++;
            st.RoundNumber++;
            st.Side = 1;
            foreach (var c in st.Creatures.Where(x => x.Side == 1))
            {
                var ow = st.FindP(c.Id == 101 ? 1 : 2);
                if (ow == null || ow.TurnNumber != 1) c.Block = 0;
            }
            // SetupPlayerTurn for P1 then P2
            foreach (var p in st.Players)
            {
                p.Energy = p.BaseMaxEnergy;
                for (int i = 0; i < 5; i++)
                {
                    if (p.Hand.Count >= 10) break;
                    if (p.Draw.Count == 0 && p.Discard.Count > 0)
                    {
                        p.Draw = RngOracle.UnstableShuffleGeneric(p.Discard, st.Rng);
                        p.Discard.Clear();
                    }
                    if (p.Draw.Count == 0) break;
                    var top = p.Draw[0];
                    p.Draw.RemoveAt(0);
                    p.Hand.Add(top);
                }
            }
        }

        switch (tok)
        {
            case "P1_BASH": PlayCard(1, 1001, 200); break;
            case "P1_STRIKE": PlayCard(1, 1002, 200); break;
            case "P1_TWIN": PlayCard(1, 1003, 200); break;
            case "P1_FPOT": UseFirePot(); break;
            case "P2_DEF": PlayCard(2, 2001, null); break;
            case "P2_STRIKEP": PlayCard(2, 2002, 200); break;
            case "P2_UPPER": PlayCard(2, 2003, 200); break;
            case "END_ROUND": EndRound(); break;
        }
        st.NextChecksumId++;
    }

    private static string EvalTimelineSeek(string[] f)
    {
        ulong seed = ulong.Parse(f[1], CultureInfo.InvariantCulture);
        int enemyHp = Math.Max(1, int.Parse(f[2], CultureInfo.InvariantCulture));
        int stride = Math.Max(1, int.Parse(f[3], CultureInfo.InvariantCulture));
        var acts = string.IsNullOrWhiteSpace(f.Length > 4 ? f[4] : "")
            ? new List<string>()
            : f[4].Split(';').Select(s => s.Trim()).Where(s => s.Length > 0).ToList();

        var init = new TSimState { Rng = new RngOracle(seed) };
        init.Creatures.Add(new TCreature { Id = 101, Entry = "IRONCLAD", Side = 1, Hp = 80, MaxHp = 80 });
        init.Creatures.Add(new TCreature { Id = 102, Entry = "SILENT", Side = 1, Hp = 70, MaxHp = 70 });
        init.Creatures.Add(new TCreature { Id = 200, Entry = "COOP_GUARDIAN", Side = 2, Hp = enemyHp, MaxHp = enemyHp, MoveId = "SLAM" });
        init.Players.Add(new TPlayer
        {
            Pid = 1, Cid = 101, Energy = 5, BaseMaxEnergy = 3, TurnNumber = 1, Potions = new List<string?> { "FIRE_POTION" },
            Hand = new()
            {
                new TCard { InstId = 1001, Entry = "BASH", Cost = 2 },
                new TCard { InstId = 1002, Entry = "STRIKE_IRONCLAD", Cost = 1 },
                new TCard { InstId = 1003, Entry = "TWIN_STRIKE", Cost = 1 }
            }
        });
        init.Players.Add(new TPlayer
        {
            Pid = 2, Cid = 102, Energy = 5, BaseMaxEnergy = 3, TurnNumber = 1, Potions = new List<string?>(),
            Hand = new()
            {
                new TCard { InstId = 2001, Entry = "DEFEND_IRONCLAD", Cost = 1 },
                new TCard { InstId = 2002, Entry = "STRIKE_IRONCLAD", Cost = 1, UpgradeLevel = 1 },
                new TCard { InstId = 2003, Entry = "UPPERCUT", Cost = 2 }
            }
        });

        var kfs = new List<(int idx, TSimState state, ulong cs)> { (0, init.Clone(), ComputeTimelineChecksum(init)) };
        var cur = init.Clone();
        for (int i = 0; i < acts.Count; i++)
        {
            TStep(cur, acts[i]);
            int stepIdx = i + 1;
            if (stepIdx % stride == 0) kfs.Add((stepIdx, cur.Clone(), ComputeTimelineChecksum(cur)));
        }

        TSimState Seek(int target)
        {
            var kf = kfs.Last(k => k.idx <= target);
            var s = kf.state.Clone();
            for (int i = kf.idx; i < Math.Min(target, acts.Count); i++) TStep(s, acts[i]);
            return s;
        }

        int mid = acts.Count / 2;
        var fullMid = init.Clone();
        for (int i = 0; i < mid; i++) TStep(fullMid, acts[i]);
        ulong fullCsum = ComputeTimelineChecksum(cur);
        bool m0 = ComputeTimelineChecksum(Seek(0)) == ComputeTimelineChecksum(init);
        bool mm = ComputeTimelineChecksum(Seek(mid)) == ComputeTimelineChecksum(fullMid);
        bool mf = ComputeTimelineChecksum(Seek(acts.Count)) == fullCsum;

        int eHp = cur.FindC(200)!.Hp;
        int p1Hp = cur.FindC(101)!.Hp;
        int p2Hp = cur.FindC(102)!.Hp;
        int p1E = cur.FindP(1)!.Energy;
        int p2E = cur.FindP(2)!.Energy;
        return $"{eHp},{p1Hp},{p2Hp},{p1E},{p2E}|{fullCsum}|{(m0 ? 1 : 0)},{(mm ? 1 : 0)},{(mf ? 1 : 0)}";
    }

    // ========================================================================
    // 12. TRACE_JSON (Versioned External Trace Wire Protocol Interop)
    // ========================================================================
    private sealed class WireModelId
    {
        [JsonPropertyName("category")] public string Category { get; set; } = "";
        [JsonPropertyName("entry")] public string Entry { get; set; } = "";
    }

    private sealed class WirePower
    {
        [JsonPropertyName("instanceId")] public int InstanceId { get; set; }
        [JsonPropertyName("modelEntry")] public string ModelEntry { get; set; } = "";
        [JsonPropertyName("powerType")] public string PowerType { get; set; } = "buff";
        [JsonPropertyName("stackType")] public string StackType { get; set; } = "counter";
        [JsonPropertyName("allowNegative")] public bool AllowNegative { get; set; }
        [JsonPropertyName("amount")] public int Amount { get; set; }
    }

    private sealed class WireCard
    {
        [JsonPropertyName("instanceId")] public int InstanceId { get; set; }
        [JsonPropertyName("modelEntry")] public string ModelEntry { get; set; } = "";
        [JsonPropertyName("ownerId")] public int OwnerId { get; set; } = 1;
        [JsonPropertyName("cardType")] public string CardType { get; set; } = "attack";
        [JsonPropertyName("rarity")] public string Rarity { get; set; } = "common";
        [JsonPropertyName("targetType")] public string TargetType { get; set; } = "anyEnemy";
        [JsonPropertyName("baseCost")] public int BaseCost { get; set; } = 1;
        [JsonPropertyName("costsX")] public bool CostsX { get; set; }
        [JsonPropertyName("starCost")] public int StarCost { get; set; }
        [JsonPropertyName("upgradeLevel")] public int UpgradeLevel { get; set; }
        [JsonPropertyName("baseDamage")] public int BaseDamage { get; set; }
        [JsonPropertyName("baseBlock")] public int BaseBlock { get; set; }
        [JsonPropertyName("gainsBlock")] public bool GainsBlock { get; set; }
    }

    private sealed class WireRelic
    {
        [JsonPropertyName("modelEntry")] public string ModelEntry { get; set; } = "";
        [JsonPropertyName("rarity")] public string Rarity { get; set; } = "common";
    }

    private sealed class WirePotion
    {
        [JsonPropertyName("modelEntry")] public string? ModelEntry { get; set; }
    }

    private sealed class WireCreature
    {
        [JsonPropertyName("id")] public int Id { get; set; }
        [JsonPropertyName("modelEntry")] public string ModelEntry { get; set; } = "";
        [JsonPropertyName("modelCategory")] public string ModelCategory { get; set; } = "MONSTER";
        [JsonPropertyName("side")] public string Side { get; set; } = "enemy";
        [JsonPropertyName("playerId")] public int? PlayerId { get; set; }
        [JsonPropertyName("currentHp")] public int CurrentHp { get; set; }
        [JsonPropertyName("maxHp")] public int MaxHp { get; set; }
        [JsonPropertyName("block")] public int Block { get; set; }
        [JsonPropertyName("powers")] public List<WirePower> Powers { get; set; } = new();
        [JsonPropertyName("monsterMoveId")] public string? MonsterMoveId { get; set; }
        [JsonPropertyName("monsterStateLog")] public List<string> MonsterStateLog { get; set; } = new();
    }

    private sealed class WirePlayer
    {
        [JsonPropertyName("playerId")] public int PlayerId { get; set; }
        [JsonPropertyName("creatureId")] public int CreatureId { get; set; }
        [JsonPropertyName("characterEntry")] public string CharacterEntry { get; set; } = "IRONCLAD";
        [JsonPropertyName("energy")] public int Energy { get; set; } = 3;
        [JsonPropertyName("baseMaxEnergy")] public int BaseMaxEnergy { get; set; } = 3;
        [JsonPropertyName("stars")] public int Stars { get; set; }
        [JsonPropertyName("turnNumber")] public int TurnNumber { get; set; } = 1;
        [JsonPropertyName("hand")] public List<WireCard> Hand { get; set; } = new();
        [JsonPropertyName("draw")] public List<WireCard> Draw { get; set; } = new();
        [JsonPropertyName("discard")] public List<WireCard> Discard { get; set; } = new();
        [JsonPropertyName("exhaust")] public List<WireCard> Exhaust { get; set; } = new();
        [JsonPropertyName("relics")] public List<WireRelic> Relics { get; set; } = new();
        [JsonPropertyName("potions")] public List<WirePotion> Potions { get; set; } = new();
    }

    private sealed class WireRng
    {
        [JsonPropertyName("counter")] public int Counter { get; set; }
        [JsonPropertyName("s0")] public string S0 { get; set; } = "";
        [JsonPropertyName("s1")] public string S1 { get; set; } = "";
        [JsonPropertyName("s2")] public string S2 { get; set; } = "";
        [JsonPropertyName("s3")] public string S3 { get; set; } = "";
        [JsonPropertyName("seed")] public string? Seed { get; set; }
    }

    private sealed class WireCombatSnapshot
    {
        [JsonPropertyName("combatId")] public int CombatId { get; set; } = 1;
        [JsonPropertyName("roundNumber")] public int RoundNumber { get; set; } = 1;
        [JsonPropertyName("currentSide")] public string CurrentSide { get; set; } = "player";
        [JsonPropertyName("isInProgress")] public bool IsInProgress { get; set; } = true;
        [JsonPropertyName("isEnding")] public bool IsEnding { get; set; }
        [JsonPropertyName("nextInstanceId")] public int NextInstanceId { get; set; } = 1000;
        [JsonPropertyName("rng")] public WireRng Rng { get; set; } = new();
        [JsonPropertyName("allies")] public List<WireCreature> Allies { get; set; } = new();
        [JsonPropertyName("enemies")] public List<WireCreature> Enemies { get; set; } = new();
        [JsonPropertyName("players")] public List<WirePlayer> Players { get; set; } = new();
    }

    private sealed class WireRunSnapshot
    {
        [JsonPropertyName("runSeed")] public string RunSeed { get; set; } = "0";
        [JsonPropertyName("currentActIndex")] public int CurrentActIndex { get; set; }
        [JsonPropertyName("ascensionLevel")] public int AscensionLevel { get; set; }
        [JsonPropertyName("gold")] public int Gold { get; set; } = 99;
        [JsonPropertyName("totalFloors")] public int TotalFloors { get; set; }
        [JsonPropertyName("currentRoom")] public string CurrentRoom { get; set; } = "unassigned";
    }

    private sealed class WireInitialState
    {
        [JsonPropertyName("run")] public WireRunSnapshot Run { get; set; } = new();
        [JsonPropertyName("combat")] public WireCombatSnapshot? Combat { get; set; }
        [JsonPropertyName("playerIds")] public List<int> PlayerIds { get; set; } = new() { 1 };
        [JsonPropertyName("nextActionId")] public int NextActionId { get; set; }
        [JsonPropertyName("nextHookId")] public int NextHookId { get; set; }
        [JsonPropertyName("nextChecksumId")] public int NextChecksumId { get; set; }
        [JsonPropertyName("isInCombat")] public bool IsInCombat { get; set; } = true;
        [JsonPropertyName("canceledCount")] public int CanceledCount { get; set; }
    }

    private sealed class WireChoiceResult
    {
        [JsonPropertyName("type")] public string Type { get; set; } = "skipped";
        [JsonPropertyName("ids")] public List<int> Ids { get; set; } = new();
        [JsonPropertyName("creatureId")] public int? CreatureId { get; set; }
        [JsonPropertyName("index")] public int? Index { get; set; }
    }

    private sealed class WireActionPayload
    {
        [JsonPropertyName("type")] public string Type { get; set; } = "";
        [JsonPropertyName("cardId")] public int? CardId { get; set; }
        [JsonPropertyName("targetId")] public int? TargetId { get; set; }
        [JsonPropertyName("slotIdx")] public int? SlotIdx { get; set; }
        [JsonPropertyName("canBackOut")] public bool CanBackOut { get; set; } = true;
        [JsonPropertyName("hookId")] public int? HookId { get; set; }
        [JsonPropertyName("row")] public int? Row { get; set; }
        [JsonPropertyName("col")] public int? Col { get; set; }
        [JsonPropertyName("relicId")] public WireModelId? RelicId { get; set; }
    }

    private sealed class WireCombatReplayEvent
    {
        [JsonPropertyName("eventType")] public string EventType { get; set; } = "none";
        [JsonPropertyName("playerId")] public int? PlayerId { get; set; }
        [JsonPropertyName("payload")] public WireActionPayload? Payload { get; set; }
        [JsonPropertyName("hookId")] public int? HookId { get; set; }
        [JsonPropertyName("actionId")] public int? ActionId { get; set; }
        [JsonPropertyName("choiceId")] public int? ChoiceId { get; set; }
        [JsonPropertyName("choiceResult")] public WireChoiceResult? ChoiceResult { get; set; }
    }

    private sealed class WireOutOfCombatSyncEvent
    {
        [JsonPropertyName("type")] public string Type { get; set; } = "";
        [JsonPropertyName("row")] public int Row { get; set; }
        [JsonPropertyName("col")] public int Col { get; set; }
        [JsonPropertyName("pointType")] public string? PointType { get; set; }
        [JsonPropertyName("roomType")] public string? RoomType { get; set; }
        [JsonPropertyName("optionKey")] public string? OptionKey { get; set; }
        [JsonPropertyName("goldDelta")] public int GoldDelta { get; set; }
        [JsonPropertyName("hpDelta")] public int HpDelta { get; set; }
        [JsonPropertyName("cardModel")] public WireModelId? CardModel { get; set; }
        [JsonPropertyName("goldCost")] public int GoldCost { get; set; }
        [JsonPropertyName("healAmt")] public int HealAmt { get; set; }
        [JsonPropertyName("goldGain")] public int GoldGain { get; set; }
        [JsonPropertyName("relicId")] public WireModelId? RelicId { get; set; }
        [JsonPropertyName("rarity")] public string Rarity { get; set; } = "common";
    }

    private sealed class WireIdDelta
    {
        [JsonPropertyName("id")] public int Id { get; set; }
        [JsonPropertyName("delta")] public int Delta { get; set; }
    }

    private sealed class WirePowerDelta
    {
        [JsonPropertyName("creatureId")] public int CreatureId { get; set; }
        [JsonPropertyName("category")] public string Category { get; set; } = "POWER";
        [JsonPropertyName("entry")] public string Entry { get; set; } = "";
        [JsonPropertyName("delta")] public int Delta { get; set; }
    }

    private sealed class WireOpaqueDelta
    {
        [JsonPropertyName("label")] public string Label { get; set; } = "opaque";
        [JsonPropertyName("hpDeltas")] public List<WireIdDelta> HpDeltas { get; set; } = new();
        [JsonPropertyName("blockDeltas")] public List<WireIdDelta> BlockDeltas { get; set; } = new();
        [JsonPropertyName("powerDeltas")] public List<WirePowerDelta> PowerDeltas { get; set; } = new();
        [JsonPropertyName("energyDeltas")] public List<WireIdDelta> EnergyDeltas { get; set; } = new();
        [JsonPropertyName("starsDeltas")] public List<WireIdDelta> StarsDeltas { get; set; } = new();
    }

    private sealed class WireTimelineEvent
    {
        [JsonPropertyName("seqIdx")] public int SeqIdx { get; set; }
        [JsonPropertyName("actIndex")] public int ActIndex { get; set; }
        [JsonPropertyName("floor")] public int Floor { get; set; } = 1;
        [JsonPropertyName("roundNumber")] public int RoundNumber { get; set; } = 1;
        [JsonPropertyName("actorPlayerId")] public int ActorPlayerId { get; set; } = 1;
        [JsonPropertyName("kind")] public string Kind { get; set; } = "";
        [JsonPropertyName("combat")] public WireCombatReplayEvent? Combat { get; set; }
        [JsonPropertyName("pauseActionId")] public int? PauseActionId { get; set; }
        [JsonPropertyName("cancelPlayCardActions")] public bool CancelPlayCardActions { get; set; }
        [JsonPropertyName("runSync")] public WireOutOfCombatSyncEvent? RunSync { get; set; }
        [JsonPropertyName("opaque")] public WireOpaqueDelta? Opaque { get; set; }
    }

    private sealed class WireChecksumEntry
    {
        [JsonPropertyName("eventIndex")] public int EventIndex { get; set; }
        [JsonPropertyName("checksum")] public string Checksum { get; set; } = "";
    }

    private sealed class WireTraceBundle
    {
        [JsonPropertyName("schemaVersion")] public int SchemaVersion { get; set; } = 1;
        [JsonPropertyName("viewerPlayerId")] public int ViewerPlayerId { get; set; } = 1;
        [JsonPropertyName("keyframeStride")] public int KeyframeStride { get; set; } = 2;
        [JsonPropertyName("initialState")] public WireInitialState InitialState { get; set; } = new();
        [JsonPropertyName("events")] public List<WireTimelineEvent> Events { get; set; } = new();
        [JsonPropertyName("expectedChecksums")] public List<WireChecksumEntry> ExpectedChecksums { get; set; } = new();
    }

    private static TCard DecodeWireCard(WireCard w) => new()
    {
        InstId = w.InstanceId,
        Entry = w.ModelEntry,
        CardType = w.CardType,
        Cost = w.CostsX ? 0 : w.BaseCost,
        UpgradeLevel = w.UpgradeLevel,
        BaseDamage = w.BaseDamage,
        BaseBlock = w.BaseBlock,
        GainsBlock = w.GainsBlock
    };

    private static TSimState DecodeWireInitialState(WireInitialState w)
    {
        ulong runSeed = ulong.TryParse(w.Run.RunSeed, NumberStyles.Integer, CultureInfo.InvariantCulture, out var rs) ? rs : 0uL;
        var st = new TSimState
        {
            RunSeed = runSeed,
            ActIndex = w.Run.CurrentActIndex,
            Gold = w.Run.Gold,
            TotalFloors = w.Run.TotalFloors,
            NextActionId = w.NextActionId,
            NextHookId = w.NextHookId,
            IsInCombat = w.IsInCombat,
            CanceledCount = w.CanceledCount,
            NextChecksumId = w.NextChecksumId,
            HasCombat = w.Combat != null
        };
        if (w.Combat != null)
        {
            var c = w.Combat;
            st.CombatId = c.CombatId;
            st.RoundNumber = c.RoundNumber;
            st.Side = c.CurrentSide == "enemy" ? 2 : (c.CurrentSide == "none" ? 0 : 1);
            st.IsInProgress = c.IsInProgress;
            st.IsEnding = c.IsEnding;
            st.NextInstanceId = c.NextInstanceId;
            if (string.IsNullOrEmpty(c.Rng.S0) && string.IsNullOrEmpty(c.Rng.S1) && !string.IsNullOrEmpty(c.Rng.Seed))
            {
                ulong rSeed = ulong.Parse(c.Rng.Seed, CultureInfo.InvariantCulture);
                var tmp = new MegaRandomOracle(rSeed);
                st.Rng = RngOracle.FromState(c.Rng.Counter, tmp.S0, tmp.S1, tmp.S2, tmp.S3);
            }
            else
            {
                ulong s0 = ulong.Parse(c.Rng.S0, CultureInfo.InvariantCulture);
                ulong s1 = ulong.Parse(c.Rng.S1, CultureInfo.InvariantCulture);
                ulong s2 = ulong.Parse(c.Rng.S2, CultureInfo.InvariantCulture);
                ulong s3 = ulong.Parse(c.Rng.S3, CultureInfo.InvariantCulture);
                st.Rng = RngOracle.FromState(c.Rng.Counter, s0, s1, s2, s3);
            }
            foreach (var cr in c.Allies.Concat(c.Enemies))
            {
                st.Creatures.Add(new TCreature
                {
                    Id = cr.Id,
                    Entry = cr.ModelEntry,
                    Side = cr.Side == "enemy" ? 2 : (cr.Side == "none" ? 0 : 1),
                    Hp = cr.CurrentHp,
                    MaxHp = cr.MaxHp,
                    Block = cr.Block,
                    MoveId = cr.MonsterMoveId ?? "",
                    StateLog = new List<string>(cr.MonsterStateLog),
                    Powers = cr.Powers.Select(pw => new TPower
                    {
                        InstId = pw.InstanceId,
                        Entry = pw.ModelEntry,
                        IsDebuff = pw.PowerType == "debuff",
                        AllowNeg = pw.AllowNegative,
                        Amt = pw.Amount
                    }).ToList()
                });
            }
            foreach (var pl in c.Players)
            {
                st.Players.Add(new TPlayer
                {
                    Pid = pl.PlayerId,
                    Cid = pl.CreatureId,
                    Energy = pl.Energy,
                    BaseMaxEnergy = pl.BaseMaxEnergy,
                    Stars = pl.Stars,
                    TurnNumber = pl.TurnNumber,
                    Relics = pl.Relics.Select(r => r.ModelEntry).ToList(),
                    Potions = pl.Potions.Select(pt => pt.ModelEntry).ToList(),
                    Hand = pl.Hand.Select(DecodeWireCard).ToList(),
                    Draw = pl.Draw.Select(DecodeWireCard).ToList(),
                    Discard = pl.Discard.Select(DecodeWireCard).ToList(),
                    Exhaust = pl.Exhaust.Select(DecodeWireCard).ToList()
                });
            }
        }
        return st;
    }

    private static int ClampIntDelta(int cur, int delta, int maxBound)
    {
        long raw = (long)cur + delta;
        return (int)Math.Min((long)maxBound, Math.Max(0L, raw));
    }

    private static void WireApplyPower(TSimState st, int targetCid, string entry, bool isDebuff, bool allowNeg, int amt)
    {
        if (st.IsEnding || amt == 0) return;
        var t = st.FindC(targetCid);
        if (t == null) return;
        var ex = t.Powers.FirstOrDefault(p => p.Entry == entry);
        if (ex != null)
        {
            if (isDebuff && entry != "ARTIFACT_POWER" && t.HasPower("ARTIFACT_POWER"))
            {
                var art = t.Powers.First(p => p.Entry == "ARTIFACT_POWER");
                art.Amt--;
                if (art.Amt <= 0) t.Powers.Remove(art);
                return;
            }
            ex.Amt = Math.Clamp(ex.Amt + amt, -StatCap, StatCap);
            bool rem = allowNeg ? ex.Amt == 0 : ex.Amt <= 0;
            if (rem) t.Powers.Remove(ex);
        }
        else
        {
            st.NextInstanceId++;
            int instId = st.NextInstanceId - 1;
            if (isDebuff && entry != "ARTIFACT_POWER" && t.HasPower("ARTIFACT_POWER"))
            {
                var art = t.Powers.First(p => p.Entry == "ARTIFACT_POWER");
                art.Amt--;
                if (art.Amt <= 0) t.Powers.Remove(art);
                return;
            }
            int clamped = Math.Clamp(amt, -StatCap, StatCap);
            bool rem = allowNeg ? clamped == 0 : clamped <= 0;
            if (!rem) t.Powers.Add(new TPower { InstId = instId, Entry = entry, IsDebuff = isDebuff, AllowNeg = allowNeg, Amt = clamped });
        }
    }

    private static void WireGainBlock(TSimState st, int targetCid, decimal baseAmt, ValuePropFlags props)
    {
        if (st.IsEnding) return;
        var t = st.FindC(targetCid);
        if (t == null || t.Hp <= 0) return;
        decimal num = baseAmt;
        if (props.IsPoweredBlock())
        {
            num += t.GetPowerAmt("DEXTERITY_POWER");
            if (t.HasPower("FRAIL_POWER")) num *= 0.75m;
        }
        num = Math.Max(0m, num);
        int gain = Math.Max(0, (int)decimal.Truncate(num));
        t.Block = Math.Min(StatCap, t.Block + gain);
    }

    private static void WireDrawCards(TSimState st, TPlayer p, int count)
    {
        for (int i = 0; i < count; i++)
        {
            if (p.Hand.Count >= 10) break;
            if (p.Draw.Count == 0 && p.Discard.Count > 0)
            {
                p.Draw = RngOracle.UnstableShuffleGeneric(p.Discard, st.Rng);
                p.Discard.Clear();
            }
            if (p.Draw.Count == 0) break;
            var top = p.Draw[0];
            p.Draw.RemoveAt(0);
            p.Hand.Add(top);
        }
    }

    private static void ReplayWireEvent(TSimState st, WireTimelineEvent ev)
    {
        if (ev.Kind == "combat" && ev.Combat != null)
        {
            var ce = ev.Combat;
            if (ce.EventType == "gameAction" && ce.Payload != null)
            {
                int pid = ce.PlayerId ?? ev.ActorPlayerId;
                var pl = ce.Payload;
                st.NextActionId++;
                if (pl.Type == "playCard" && pl.CardId.HasValue)
                {
                    var p = st.FindP(pid);
                    var card = p?.Hand.FirstOrDefault(c => c.InstId == pl.CardId.Value);
                    if (p != null && card != null && p.Energy >= card.Cost)
                    {
                        p.Energy -= card.Cost;
                        p.Hand.Remove(card);
                        bool upg = card.UpgradeLevel > 0;
                        decimal DmgOr(int d) => card.BaseDamage == 0 ? (decimal)d : (decimal)card.BaseDamage;
                        decimal BlkOr(int b) => card.BaseBlock == 0 ? (decimal)b : (decimal)card.BaseBlock;
                        switch (card.Entry)
                        {
                            case "STRIKE_IRONCLAD": case "STRIKE_SILENT": case "STRIKE_DEFECT": case "STRIKE_NECROBINDER": case "STRIKE_REGENT":
                                if (pl.TargetId.HasValue) TApplyDamageHit(st, p.Cid, pl.TargetId.Value, DmgOr(upg ? 9 : 6), ValuePropFlags.Move);
                                break;
                            case "DEFEND_IRONCLAD": case "DEFEND_SILENT": case "DEFEND_DEFECT": case "DEFEND_NECROBINDER": case "DEFEND_REGENT":
                                WireGainBlock(st, p.Cid, BlkOr(upg ? 8 : 5), ValuePropFlags.Move);
                                break;
                            case "BASH":
                                if (pl.TargetId.HasValue)
                                {
                                    TApplyDamageHit(st, p.Cid, pl.TargetId.Value, DmgOr(upg ? 10 : 8), ValuePropFlags.Move);
                                    WireApplyPower(st, pl.TargetId.Value, "VULNERABLE_POWER", true, false, upg ? 3 : 2);
                                }
                                break;
                            case "TWIN_STRIKE":
                                if (pl.TargetId.HasValue)
                                {
                                    TApplyDamageHit(st, p.Cid, pl.TargetId.Value, DmgOr(upg ? 7 : 5), ValuePropFlags.Move);
                                    TApplyDamageHit(st, p.Cid, pl.TargetId.Value, DmgOr(upg ? 7 : 5), ValuePropFlags.Move);
                                }
                                break;
                            case "POMMEL_STRIKE":
                                if (pl.TargetId.HasValue) TApplyDamageHit(st, p.Cid, pl.TargetId.Value, DmgOr(upg ? 10 : 9), ValuePropFlags.Move);
                                WireDrawCards(st, p, upg ? 2 : 1);
                                break;
                            case "IRON_WAVE":
                                WireGainBlock(st, p.Cid, BlkOr(upg ? 7 : 5), ValuePropFlags.Move);
                                if (pl.TargetId.HasValue) TApplyDamageHit(st, p.Cid, pl.TargetId.Value, DmgOr(upg ? 7 : 5), ValuePropFlags.Move);
                                break;
                            case "CLEAVE":
                                foreach (var en in st.Creatures.Where(x => x.Side == 2 && x.Hp > 0))
                                    TApplyDamageHit(st, p.Cid, en.Id, DmgOr(upg ? 11 : 8), ValuePropFlags.Move);
                                break;
                            case "CLOTHESLINE":
                                if (pl.TargetId.HasValue)
                                {
                                    TApplyDamageHit(st, p.Cid, pl.TargetId.Value, DmgOr(upg ? 14 : 12), ValuePropFlags.Move);
                                    WireApplyPower(st, pl.TargetId.Value, "WEAK_POWER", true, false, upg ? 3 : 2);
                                }
                                break;
                            case "UPPERCUT":
                                if (pl.TargetId.HasValue)
                                {
                                    int amt = upg ? 2 : 1;
                                    TApplyDamageHit(st, p.Cid, pl.TargetId.Value, DmgOr(13), ValuePropFlags.Move);
                                    WireApplyPower(st, pl.TargetId.Value, "WEAK_POWER", true, false, amt);
                                    WireApplyPower(st, pl.TargetId.Value, "VULNERABLE_POWER", true, false, amt);
                                }
                                break;
                            case "BLUDGEON":
                                if (pl.TargetId.HasValue) TApplyDamageHit(st, p.Cid, pl.TargetId.Value, DmgOr(upg ? 42 : 32), ValuePropFlags.Move);
                                break;
                            case "INFLAME":
                                WireApplyPower(st, p.Cid, "STRENGTH_POWER", false, true, upg ? 3 : 2);
                                break;
                            case "FOOTWORK":
                                WireApplyPower(st, p.Cid, "DEXTERITY_POWER", false, true, upg ? 3 : 2);
                                break;
                            case "SHRUG_IT_OFF":
                                WireGainBlock(st, p.Cid, BlkOr(upg ? 11 : 8), ValuePropFlags.Move);
                                WireDrawCards(st, p, 1);
                                break;
                            case "NEUTRALIZE":
                                if (pl.TargetId.HasValue)
                                {
                                    TApplyDamageHit(st, p.Cid, pl.TargetId.Value, DmgOr(upg ? 4 : 3), ValuePropFlags.Move);
                                    WireApplyPower(st, pl.TargetId.Value, "WEAK_POWER", true, false, upg ? 2 : 1);
                                }
                                break;
                            default:
                                if (card.CardType == "attack" && card.BaseDamage > 0 && pl.TargetId.HasValue)
                                    TApplyDamageHit(st, p.Cid, pl.TargetId.Value, card.BaseDamage, ValuePropFlags.Move);
                                else if (card.GainsBlock && card.BaseBlock > 0)
                                    WireGainBlock(st, p.Cid, card.BaseBlock, ValuePropFlags.Move);
                                break;
                        }
                        if (card.CardType != "power") p.Discard.Add(card);
                        TCheckWin(st);
                    }
                }
                else if (pl.Type == "usePotion" && pl.SlotIdx.HasValue)
                {
                    int slot = pl.SlotIdx.Value;
                    var p = st.FindP(pid);
                    if (st.IsInProgress && p != null && slot >= 0 && slot < p.Potions.Count && p.Potions[slot] != null)
                    {
                        string potEntry = p.Potions[slot]!;
                        p.Potions[slot] = null;
                        switch (potEntry)
                        {
                            case "FIRE_POTION":
                                if (pl.TargetId.HasValue) TApplyDamageHit(st, p.Cid, pl.TargetId.Value, 20m, ValuePropFlags.Move | ValuePropFlags.Unpowered);
                                break;
                            case "BLOCK_POTION":
                                WireGainBlock(st, p.Cid, 12m, ValuePropFlags.Move | ValuePropFlags.Unpowered);
                                break;
                            case "STRENGTH_POTION":
                                WireApplyPower(st, p.Cid, "STRENGTH_POWER", false, true, 2);
                                break;
                            case "FEAR_POTION":
                                if (pl.TargetId.HasValue) WireApplyPower(st, pl.TargetId.Value, "VULNERABLE_POWER", true, false, 3);
                                break;
                            case "WEAK_POTION":
                                if (pl.TargetId.HasValue) WireApplyPower(st, pl.TargetId.Value, "WEAK_POWER", true, false, 3);
                                break;
                            case "ENERGY_POTION":
                                p.Energy = Math.Min(StatCap, p.Energy + 2);
                                break;
                            case "SWIFT_POTION":
                                WireDrawCards(st, p, 3);
                                break;
                            case "HEAL_POTION":
                            {
                                var selfC = st.FindC(p.Cid);
                                if (selfC != null && !st.IsEnding && selfC.Hp > 0)
                                    selfC.Hp = Math.Min(selfC.MaxHp, selfC.Hp + 10);
                                break;
                            }
                        }
                        TCheckWin(st);
                    }
                }
                else if (pl.Type == "discardPotion" && pl.SlotIdx.HasValue)
                {
                    int slot = pl.SlotIdx.Value;
                    var p = st.FindP(pid);
                    if (p != null && slot >= 0 && slot < p.Potions.Count) p.Potions[slot] = null;
                }
            }
            else if (ce.EventType == "hookAction")
            {
                int hid = ce.HookId ?? st.NextHookId;
                st.NextHookId = Math.Max(st.NextHookId, hid + 1);
                st.NextActionId++;
            }
        }
        else if (ev.Kind == "endRoundAndRunEnemies" && st.HasCombat && st.IsInProgress)
        {
            foreach (var p in st.Players)
            {
                foreach (var c in p.Hand.ToList()) { p.Hand.Remove(c); p.Discard.Add(c); }
            }
            st.Side = 2;
            foreach (var c in st.Creatures.Where(x => x.Side == 2)) c.Block = 0;
            foreach (var en in st.Creatures.Where(x => x.Side == 2 && x.Hp > 0).ToList())
            {
                if (!st.IsInProgress) break;
                if (en.Entry == "COOP_GUARDIAN")
                {
                    string move = en.StateLog.Count == 0 ? (string.IsNullOrEmpty(en.MoveId) ? "SLAM" : en.MoveId) : (en.MoveId == "SLAM" ? "FORTIFY" : "SLAM");
                    en.MoveId = move;
                    en.StateLog.Add(move);
                    if (move == "SLAM")
                    {
                        foreach (var ally in st.Creatures.Where(c => c.Side == 1 && c.Hp > 0))
                            TApplyDamageHit(st, en.Id, ally.Id, 7m, ValuePropFlags.Move);
                    }
                    else
                    {
                        WireGainBlock(st, en.Id, 8m, ValuePropFlags.Move);
                        WireApplyPower(st, en.Id, "STRENGTH_POWER", false, true, 1);
                    }
                }
                else if (en.Entry == "CULTIST")
                {
                    string move = en.StateLog.Count == 0 ? (string.IsNullOrEmpty(en.MoveId) ? "INCANT" : en.MoveId) : "DARK_STRIKE";
                    en.MoveId = move;
                    en.StateLog.Add(move);
                    if (move == "INCANT")
                    {
                        WireApplyPower(st, en.Id, "STRENGTH_POWER", false, true, 3);
                    }
                    else
                    {
                        var firstAlly = st.Creatures.FirstOrDefault(c => c.Side == 1 && c.Hp > 0);
                        if (firstAlly != null) TApplyDamageHit(st, en.Id, firstAlly.Id, 6m, ValuePropFlags.Move);
                    }
                }
            }
            TCheckWin(st);
            if (st.IsInProgress)
            {
                foreach (var p in st.Players) p.TurnNumber++;
                st.RoundNumber++;
                st.Side = 1;
                foreach (var c in st.Creatures.Where(x => x.Side == 1))
                {
                    var ow = st.Players.FirstOrDefault(x => x.Cid == c.Id);
                    if (ow == null || ow.TurnNumber != 1) c.Block = 0;
                }
                foreach (var p in st.Players)
                {
                    p.Energy = p.BaseMaxEnergy;
                    WireDrawCards(st, p, 5);
                }
            }
        }
        else if (ev.Kind == "opaqueStep" && ev.Opaque != null && st.HasCombat)
        {
            var d = ev.Opaque;
            foreach (var h in d.HpDeltas)
            {
                var c = st.FindC(h.Id);
                if (c != null) c.Hp = ClampIntDelta(c.Hp, h.Delta, c.MaxHp);
            }
            foreach (var b in d.BlockDeltas)
            {
                var c = st.FindC(b.Id);
                if (c != null) c.Block = ClampIntDelta(c.Block, b.Delta, StatCap);
            }
            foreach (var pw in d.PowerDeltas)
            {
                var c = st.FindC(pw.CreatureId);
                if (c == null) continue;
                var ex = c.Powers.FirstOrDefault(x => x.Entry == pw.Entry);
                if (ex != null)
                {
                    ex.Amt = Math.Clamp(ex.Amt + pw.Delta, -StatCap, StatCap);
                    bool rem = ex.AllowNeg ? ex.Amt == 0 : ex.Amt <= 0;
                    if (rem) c.Powers.Remove(ex);
                }
                else if (pw.Delta != 0)
                {
                    int newId = st.NextInstanceId++;
                    bool allowNeg = pw.Delta < 0;
                    int clamped = Math.Clamp(pw.Delta, -StatCap, StatCap);
                    bool rem = allowNeg ? clamped == 0 : clamped <= 0;
                    if (!rem) c.Powers.Add(new TPower { InstId = newId, Entry = pw.Entry, IsDebuff = pw.Delta < 0, AllowNeg = allowNeg, Amt = clamped });
                }
            }
            foreach (var eg in d.EnergyDeltas)
            {
                var p = st.FindP(eg.Id);
                if (p != null) p.Energy = ClampIntDelta(p.Energy, eg.Delta, StatCap);
            }
            foreach (var sr in d.StarsDeltas)
            {
                var p = st.FindP(sr.Id);
                if (p != null) p.Stars = ClampIntDelta(p.Stars, sr.Delta, StatCap);
            }
        }
        else if (ev.Kind == "runSync" && ev.RunSync != null)
        {
            var rs = ev.RunSync;
            switch (rs.Type)
            {
                case "mapMove": st.TotalFloors++; break;
                case "eventChoice": st.Gold = ClampIntDelta(st.Gold, rs.GoldDelta, StatCap); break;
                case "merchantBuy": st.Gold -= Math.Min(st.Gold, rs.GoldCost); break;
                case "rewardPick": st.Gold += rs.GoldGain; break;
                case "actAdvance": st.ActIndex++; break;
            }
        }
        st.NextChecksumId++;
    }

    private static (List<(int idx, TSimState state, ulong cs)> kfs, TSimState finalSt) BuildWireArchive(WireTraceBundle b)
    {
        var init = DecodeWireInitialState(b.InitialState);
        int stride = Math.Max(1, b.KeyframeStride);
        var kfs = new List<(int idx, TSimState state, ulong cs)> { (0, init.Clone(), ComputeTimelineChecksum(init)) };
        var cur = init.Clone();
        for (int i = 0; i < b.Events.Count; i++)
        {
            ReplayWireEvent(cur, b.Events[i]);
            int stepIdx = i + 1;
            if (stepIdx % stride == 0) kfs.Add((stepIdx, cur.Clone(), ComputeTimelineChecksum(cur)));
        }
        return (kfs, cur);
    }

    private static TSimState SeekWire(List<(int idx, TSimState state, ulong cs)> kfs, List<WireTimelineEvent> events, int target)
    {
        var kf = kfs.Last(k => k.idx <= target);
        var s = kf.state.Clone();
        for (int i = kf.idx; i < Math.Min(target, events.Count); i++) ReplayWireEvent(s, events[i]);
        return s;
    }

    private static string EvalTraceJson(string rawJson)
    {
        var b = JsonSerializer.Deserialize<WireTraceBundle>(rawJson);
        if (b == null || b.SchemaVersion != 1) return "ERR:invalid_bundle";
        var (kfs, cur) = BuildWireArchive(b);
        int n = b.Events.Count;
        int mid = n / 2;
        ulong c0 = ComputeTimelineChecksum(SeekWire(kfs, b.Events, 0));
        ulong cMid = ComputeTimelineChecksum(SeekWire(kfs, b.Events, mid));
        ulong cFin = ComputeTimelineChecksum(SeekWire(kfs, b.Events, n));

        // JSON serializer roundtrip check
        string rtJson = JsonSerializer.Serialize(b);
        var b2 = JsonSerializer.Deserialize<WireTraceBundle>(rtJson);
        bool rtOk = b2 != null && b2.SchemaVersion == 1;
        if (rtOk)
        {
            var (kfs2, _) = BuildWireArchive(b2!);
            rtOk = ComputeTimelineChecksum(SeekWire(kfs2, b2!.Events, 0)) == c0 &&
                   ComputeTimelineChecksum(SeekWire(kfs2, b2!.Events, mid)) == cMid &&
                   ComputeTimelineChecksum(SeekWire(kfs2, b2!.Events, n)) == cFin;
        }
        int eHp = cur.HasCombat ? (cur.FindC(200)?.Hp ?? 0) : 0;
        int p1Hp = cur.HasCombat ? (cur.FindC(101)?.Hp ?? 0) : 0;
        int p2Hp = cur.HasCombat ? (cur.FindC(102)?.Hp ?? 0) : 0;
        int p1E = cur.HasCombat ? (cur.FindP(1)?.Energy ?? 0) : 0;
        int p2E = cur.HasCombat ? (cur.FindP(2)?.Energy ?? 0) : 0;
        return $"{eHp},{p1Hp},{p2Hp},{p1E},{p2E}|{c0},{cMid},{cFin}|{(rtOk ? 1 : 0)}";
    }

    private static WireTraceBundle CreateSampleWireBundle()
    {
        var r = new MegaRandomOracle(42uL);
        var b = new WireTraceBundle
        {
            SchemaVersion = 1,
            ViewerPlayerId = 1,
            KeyframeStride = 2,
            InitialState = new WireInitialState
            {
                Run = new WireRunSnapshot { RunSeed = "42", CurrentActIndex = 0, AscensionLevel = 0, Gold = 99, TotalFloors = 1, CurrentRoom = "monster" },
                PlayerIds = new List<int> { 1, 2 },
                IsInCombat = true,
                Combat = new WireCombatSnapshot
                {
                    CombatId = 1,
                    RoundNumber = 1,
                    CurrentSide = "player",
                    IsInProgress = true,
                    IsEnding = false,
                    NextInstanceId = 1000,
                    Rng = new WireRng { Counter = 0, S0 = r.S0.ToString(CultureInfo.InvariantCulture), S1 = r.S1.ToString(CultureInfo.InvariantCulture), S2 = r.S2.ToString(CultureInfo.InvariantCulture), S3 = r.S3.ToString(CultureInfo.InvariantCulture) },
                    Allies = new List<WireCreature>
                    {
                        new() { Id = 101, ModelEntry = "IRONCLAD", ModelCategory = "CHARACTER", Side = "player", PlayerId = 1, CurrentHp = 80, MaxHp = 80 },
                        new() { Id = 102, ModelEntry = "SILENT", ModelCategory = "CHARACTER", Side = "player", PlayerId = 2, CurrentHp = 70, MaxHp = 70 }
                    },
                    Enemies = new List<WireCreature>
                    {
                        new() { Id = 200, ModelEntry = "COOP_GUARDIAN", ModelCategory = "MONSTER", Side = "enemy", CurrentHp = 34, MaxHp = 34, MonsterMoveId = "SLAM" }
                    },
                    Players = new List<WirePlayer>
                    {
                        new()
                        {
                            PlayerId = 1, CreatureId = 101, CharacterEntry = "IRONCLAD", Energy = 3, BaseMaxEnergy = 3,
                            Potions = new List<WirePotion> { new() { ModelEntry = "FIRE_POTION" } },
                            Hand = new List<WireCard> { new() { InstanceId = 1001, ModelEntry = "BASH", OwnerId = 1, BaseCost = 2 } }
                        },
                        new()
                        {
                            PlayerId = 2, CreatureId = 102, CharacterEntry = "SILENT", Energy = 3, BaseMaxEnergy = 3,
                            Hand = new List<WireCard>
                            {
                                new() { InstanceId = 2001, ModelEntry = "TWIN_STRIKE", OwnerId = 2, BaseCost = 1 },
                                new() { InstanceId = 2002, ModelEntry = "STRIKE_IRONCLAD", OwnerId = 2, BaseCost = 1, UpgradeLevel = 1 }
                            }
                        }
                    }
                }
            },
            Events = new List<WireTimelineEvent>
            {
                new() { SeqIdx = 0, Floor = 1, RoundNumber = 1, ActorPlayerId = 1, Kind = "combat", Combat = new WireCombatReplayEvent { EventType = "gameAction", PlayerId = 1, Payload = new WireActionPayload { Type = "playCard", CardId = 1001, TargetId = 200 } } },
                new() { SeqIdx = 1, Floor = 1, RoundNumber = 1, ActorPlayerId = 2, Kind = "combat", Combat = new WireCombatReplayEvent { EventType = "gameAction", PlayerId = 2, Payload = new WireActionPayload { Type = "playCard", CardId = 2001, TargetId = 200 } } },
                new() { SeqIdx = 2, Floor = 1, RoundNumber = 1, ActorPlayerId = 1, Kind = "opaqueStep", Opaque = new WireOpaqueDelta { Label = "MOD_BONUS", BlockDeltas = new() { new WireIdDelta { Id = 101, Delta = 5 } } } }
            }
        };
        var (kfs, _) = BuildWireArchive(b);
        b.ExpectedChecksums = kfs.Select(k => new WireChecksumEntry { EventIndex = k.idx, Checksum = k.cs.ToString(CultureInfo.InvariantCulture) }).ToList();
        return b;
    }

    private static string EvalLine(string line)
    {
        string[] f = line.Split('\t');
        return f[0] switch
        {
            "RNG_SEQ"       => EvalRngSeq(f[1], f[2]),
            "RNG_SHUFFLE"   => EvalRngShuffle(f[1], f.Length > 2 ? f[2] : ""),
            "DMG_PIPE"      => EvalDmgPipe(f),
            "BLK_PIPE"      => EvalBlkPipe(f),
            "CREATURE_DMG"  => EvalCreatureDmg(f),
            "POWER_STACK"   => EvalPowerStack(f),
            "CARD_COST"     => EvalCardCost(f),
            "RARITY_ODDS"   => EvalRarityOdds(f),
            "MOD_SORT"      => EvalModSort(f),
            "QUEUE_SET"     => EvalQueueSet(f),
            "TIMELINE_SEEK" => EvalTimelineSeek(f),
            "TRACE_JSON"    => EvalTraceJson(f[1]),
            _               => $"UNKNOWN_OP:{f[0]}"
        };
    }

    public static int Main(string[] args)
    {
        if (args.Length == 2 && args[0] == "--export-sample-trace")
        {
            var bundle = CreateSampleWireBundle();
            string json = JsonSerializer.Serialize(bundle, new JsonSerializerOptions { WriteIndented = true });
            File.WriteAllText(args[1], json);
            Console.WriteLine($"Exported C# sample trace bundle to {args[1]}");
            return 0;
        }
        if (args.Length == 2 && args[0] == "--verify-trace")
        {
            var b = JsonSerializer.Deserialize<WireTraceBundle>(File.ReadAllText(args[1]));
            if (b == null || b.SchemaVersion != 1)
            {
                Console.Error.WriteLine("VERIFY_FAILED: unsupported or malformed trace JSON");
                return 1;
            }
            var (kfs, _) = BuildWireArchive(b);
            var mismatches = new List<string>();
            foreach (var exp in b.ExpectedChecksums)
            {
                var stAt = SeekWire(kfs, b.Events, exp.EventIndex);
                string act = ComputeTimelineChecksum(stAt).ToString(CultureInfo.InvariantCulture);
                if (act != exp.Checksum)
                    mismatches.Add($"step#{exp.EventIndex}: expected={exp.Checksum} actual={act}");
            }
            if (mismatches.Count > 0)
            {
                foreach (var m in mismatches) Console.Error.WriteLine($"MISMATCH {m}");
                return 1;
            }
            Console.WriteLine($"VERIFIED_OK (checked={b.ExpectedChecksums.Count})");
            return 0;
        }
        if (args.Length != 2 || args[0] != "--diff")
        {
            Console.Error.WriteLine("Usage: Sts2Oracle --diff <input.tsv> | --export-sample-trace <out.json> | --verify-trace <in.json>");
            return 2;
        }
        foreach (string raw in File.ReadLines(args[1]))
        {
            string trimmed = raw.Trim();
            if (trimmed.Length == 0) continue;
            Console.WriteLine(EvalLine(trimmed));
        }
        return 0;
    }
}
