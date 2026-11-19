using System.Globalization;
using System.Numerics;
using System.Text;

namespace Sts2Oracle;

// Reference C# oracle ported directly from `reference/sts2/` for bit-exact
// differential verification against the Lean 4 `Sts2Model` / `sts2sim`.

internal sealed class MegaRandomOracle
{
    private const double IncrDouble = 1.1102230246251565E-16;
    private ulong _s0, _s1, _s2, _s3;

    public MegaRandomOracle(ulong seed)
    {
        _s0 = Splitmix64(ref seed);
        _s1 = Splitmix64(ref seed);
        _s2 = Splitmix64(ref seed);
        _s3 = Splitmix64(ref seed);
    }

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
    public RngOracle(ulong seed) => _random = new MegaRandomOracle(seed);
    public ulong NextUnsignedLong() => _random.NextULongInner();
    public int NextInt(int maxExclusive) => _random.Next(maxExclusive);
    public bool NextBool() => _random.Next(2) == 0;
    public double NextDouble() => _random.NextDouble();
    public float NextFloat() => (float)_random.NextDouble();

    public static List<long> UnstableShuffle(List<long> list, RngOracle rng)
    {
        var copy = new List<long>(list);
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

    private static string EvalLine(string line)
    {
        string[] f = line.Split('\t');
        return f[0] switch
        {
            "RNG_SEQ"      => EvalRngSeq(f[1], f[2]),
            "RNG_SHUFFLE"  => EvalRngShuffle(f[1], f.Length > 2 ? f[2] : ""),
            "DMG_PIPE"     => EvalDmgPipe(f),
            "BLK_PIPE"     => EvalBlkPipe(f),
            "CREATURE_DMG" => EvalCreatureDmg(f),
            "POWER_STACK"  => EvalPowerStack(f),
            "CARD_COST"    => EvalCardCost(f),
            "RARITY_ODDS"  => EvalRarityOdds(f),
            "MOD_SORT"     => EvalModSort(f),
            _              => $"UNKNOWN_OP:{f[0]}"
        };
    }

    public static int Main(string[] args)
    {
        if (args.Length != 2 || args[0] != "--diff")
        {
            Console.Error.WriteLine("Usage: Sts2Oracle --diff <input.tsv>");
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
