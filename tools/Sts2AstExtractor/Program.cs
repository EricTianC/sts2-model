using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Text;

namespace Sts2AstExtractor;

internal enum IrTarget
{
    Self,
    ChosenTarget,
    AllEnemies,
    RandomEnemy,
    AllAllies,
    FirstLivingPlayer
}

internal enum IrOrbKind
{
    Lightning,
    Frost,
    Dark,
    Plasma,
    Glass
}

internal sealed record PowerMeta(
    string ClassName,
    string EntryId,
    string PowerType,
    string StackType,
    string InstanceType,
    bool AllowNegative);

internal sealed record CardMeta(
    string ClassName,
    string EntryId,
    string CardType,
    int BaseCost,
    string Rarity,
    string TargetType,
    bool CostsX,
    int BaseStarCost,
    string[] Keywords,
    string[] Tags);

internal sealed record CardUpgradeMeta(int Cost, string[] Keywords);

internal sealed record AscVal(int Threshold, int AscValue, int BaseValue)
{
    public static AscVal Const(int v) => new(0, v, v);
    public bool IsConst => Threshold == 0 && AscValue == BaseValue;
}

internal sealed record IrProps(bool Unpowered, bool Unblockable, bool IsCard, bool IsMonster, bool Move = true);

internal abstract record IrOp;
internal sealed record OpDealDamage(IrTarget Target, decimal Amount, int Hits, IrProps Props) : IrOp;
internal sealed record OpGainBlock(IrTarget Target, decimal Amount, IrProps Props) : IrOp;
internal sealed record OpApplyPower(IrTarget Target, PowerMeta Power, decimal Amount) : IrOp;
internal sealed record OpRemovePower(IrTarget Target, string PowerEntryId) : IrOp;
internal sealed record OpDraw(int Count) : IrOp;
internal sealed record OpDiscardChosen(int ChoiceId, int Count) : IrOp;
internal sealed record OpDiscardAllHand() : IrOp;
internal sealed record OpExhaustSelf() : IrOp;
internal sealed record OpExhaustChosen(int ChoiceId, int Count) : IrOp;
internal sealed record OpGainEnergy(int Amount) : IrOp;
internal sealed record OpGainStars(int Amount) : IrOp;
internal sealed record OpHeal(IrTarget Target, decimal Amount) : IrOp;
internal sealed record OpChannelOrb(IrOrbKind Kind) : IrOp;
internal sealed record OpEvokeOrb(int Times) : IrOp;
internal sealed record OpForge(decimal Amount) : IrOp;
internal sealed record OpAddGeneratedCard(string CardEntry, string CardType, int Cost, string Pile, int Count, string Pos) : IrOp;
internal sealed record OpSummonOsty(decimal Amount) : IrOp;
internal sealed record OpDealDamageAsc(IrTarget Target, AscVal Amt, int Hits, IrProps Props) : IrOp;
internal sealed record OpGainBlockAsc(IrTarget Target, AscVal Amt, IrProps Props) : IrOp;
internal sealed record OpApplyPowerAsc(IrTarget Target, PowerMeta Power, AscVal Amt) : IrOp;
internal enum ValueSource { ActorBlock, ChosenBlock, DiscardCount }
internal enum IrKind
{
    AddOrbSlots, RemoveOrbSlots, AddPlayedCardCombatCost, DealDamageValue, GainBlockValue,
    GainCurrentEnergy, ApplyPowerIfPresent, DealDamageIfPower, DrawIfNoAttacks
}
internal readonly record struct RuntimeValue(ValueSource Source, decimal Base, decimal Multiplier);
internal readonly record struct PowerHitCount(IrTarget Target, PowerMeta Power, int Present, int Otherwise);
internal sealed record OpAddOrbSlots(int Count) : IrOp;
internal sealed record OpRemoveOrbSlots(int Count) : IrOp;
internal sealed record OpAddPlayedCardCombatCost(int Amount) : IrOp;
internal sealed record OpDealDamageValue(IrTarget Target, RuntimeValue Value, int Hits, IrProps Props) : IrOp;
internal sealed record OpGainBlockValue(IrTarget Target, RuntimeValue Value, IrProps Props) : IrOp;
internal sealed record OpGainCurrentEnergy() : IrOp;
internal sealed record OpApplyPowerIfPresent(IrTarget Target, PowerMeta Power, decimal Amount) : IrOp;
internal sealed record OpDealDamageIfPower(IrTarget Target, PowerHitCount HitCount, decimal Amount, IrProps Props) : IrOp;
internal sealed record OpDrawIfNoAttacks(int Count) : IrOp;

internal sealed record ExtractedCard(
    string EntryId,
    string ClassName,
    string FileName,
    CardUpgradeMeta Upgrade,
    List<IrOp> BaseOps,
    List<IrOp> UpgradedOps);

internal sealed record ExtractedPotion(
    string EntryId,
    string ClassName,
    List<IrOp> Ops);

internal sealed record MonsterNodeSpec(
    string Id,
    string FollowUpId,
    bool IsRandomBranch,
    List<(string TargetId, int Weight)> RandomTargets,
    bool MustPerformOnce);

internal sealed record MonsterMoveSpec(
    string MoveId,
    List<IrOp> Ops);

internal sealed record ExtractedMonster(
    string EntryId,
    string ClassName,
    string InitialStateId,
    List<MonsterNodeSpec> Nodes,
    List<MonsterMoveSpec> Moves);

internal sealed record SkipRecord(
    string Category, string FileName, string EntryId, string Reason, string Detail, LinePosition? Position = null);

internal sealed class DynamicVarEntry
{
    public string Key { get; init; } = "";
    public string Kind { get; init; } = "";
    public decimal BaseValue { get; set; }
    public bool Unpowered { get; init; }
    public bool Unblockable { get; init; }
    public ExpressionSyntax? DeclaredProps { get; init; }
    public ValueSource? CalculatedSource { get; init; }

    public DynamicVarEntry Clone() => new()
    {
        Key = Key,
        Kind = Kind,
        BaseValue = BaseValue,
        Unpowered = Unpowered,
        Unblockable = Unblockable,
        DeclaredProps = DeclaredProps,
        CalculatedSource = CalculatedSource
    };
}

internal static class Program
{
    private const int ChunkSize = 25;

    private static readonly Regex SlugRegex = new(@"(?<=[A-Za-z0-9])([A-Z])", RegexOptions.Compiled);
    private static readonly Regex CleanSlugRegex = new(@"[^A-Z0-9_]", RegexOptions.Compiled);

    private static readonly Dictionary<string, int> AscensionThresholds = new(StringComparer.Ordinal)
    {
        ["None"] = 0,
        ["SwarmingElites"] = 1,
        ["WearyTraveler"] = 2,
        ["Poverty"] = 3,
        ["TightBelt"] = 4,
        ["AscendersBane"] = 5,
        ["Gloom"] = 6,
        ["Scarcity"] = 7,
        ["ToughEnemies"] = 8,
        ["DeadlyEnemies"] = 9,
        ["DoubleBoss"] = 10
    };

    private static readonly HashSet<string> AllowedCardNonHookMethods = new(StringComparer.Ordinal)
    {
        "OnPlay", "OnUpgrade", "OnKeywords", "CreateUpgradePreview", "GetVfxPath", "GetSfxPath",
        "GetPortraitPath", "GetBetaPortraitPath", "ShouldGlowGoldInternal", "ShouldGlowRedInternal"
    };

    private static readonly HashSet<string> AllowedMonsterNonHookMethods = new(StringComparer.Ordinal)
    {
        "GenerateMoveStateMachine", "SetupSkins", "GenerateAnimator", "ShouldShowMoveInBestiary",
        "PlayAttackSfx", "PlayDeathSfx", "PlayHitSfx", "UpdateVfx", "SetupVfx", "OnSpawnAnimation",
        "GetBestiaryMoves", "CreateVisuals", "AfterAddedToRoom"
    };

    private static string Slugify(string raw)
    {
        string step1 = SlugRegex.Replace(raw.Trim(), "_$1").ToUpperInvariant().Replace(' ', '_');
        return CleanSlugRegex.Replace(step1, "");
    }

    public static int Main(string[] args)
    {
        string repoRoot = args.Length > 0 ? Path.GetFullPath(args[0]) : FindRepoRoot(Directory.GetCurrentDirectory());
        string refRoot = Path.Combine(repoRoot, "reference", "sts2");
        if (!Directory.Exists(refRoot))
        {
            Console.Error.WriteLine($"Reference directory not found: {refRoot}");
            return 1;
        }

        var powers = LoadPowerMetadata(Path.Combine(refRoot, "MegaCrit.Sts2.Core.Models.Powers"));
        var cardMetas = LoadCardMetadata(Path.Combine(refRoot, "MegaCrit.Sts2.Core.Models.Cards"));

        var skips = new List<SkipRecord>();
        var cards = ExtractCards(Path.Combine(refRoot, "MegaCrit.Sts2.Core.Models.Cards"), powers, cardMetas, skips);
        var potions = ExtractPotions(Path.Combine(refRoot, "MegaCrit.Sts2.Core.Models.Potions"), powers, cardMetas, skips);
        var monsters = ExtractMonsters(Path.Combine(refRoot, "MegaCrit.Sts2.Core.Models.Monsters"), powers, skips);

        cards.Sort((a, b) => StringComparer.Ordinal.Compare(a.EntryId, b.EntryId));
        potions.Sort((a, b) => StringComparer.Ordinal.Compare(a.EntryId, b.EntryId));
        monsters.Sort((a, b) => StringComparer.Ordinal.Compare(a.EntryId, b.EntryId));

        string genDir = Path.Combine(repoRoot, "Sts2Model", "Sim", "Generated");
        Directory.CreateDirectory(genDir);

        WriteTypesLean(Path.Combine(genDir, "Types.lean"));
        WriteCardsLean(Path.Combine(genDir, "Cards.lean"), cards);
        WritePotionsLean(Path.Combine(genDir, "Potions.lean"), potions);
        WriteMonstersLean(Path.Combine(genDir, "Monsters.lean"), monsters);
        WriteVerifyLean(Path.Combine(genDir, "Verify.lean"), cards, potions, monsters);

        string oracleDataPath = Path.Combine(repoRoot, "DiffTest", "Sts2Oracle", "Tier2OracleData.cs");
        WriteTier2OracleDataCs(oracleDataPath, cards, potions, monsters);

        string auditPath = Path.Combine(repoRoot, "docs", "tier2_extraction_audit.md");
        WriteAuditMarkdown(auditPath, cards, potions, monsters, skips);
        string cardAuditPath = Path.Combine(repoRoot, "docs", "tier2_cards.json");
        WriteCardManifest(cardAuditPath, cards, cardMetas, skips);

        int totalCards = cards.Count + skips.Count(s => s.Category == "Card");
        int totalPotions = potions.Count + skips.Count(s => s.Category == "Potion");
        int totalMonsters = monsters.Count + skips.Count(s => s.Category == "Monster");

        Console.WriteLine("Tier-2 Roslyn AST Extraction Complete:");
        Console.WriteLine($"  Powers   : {powers.Count} metadata entries loaded");
        Console.WriteLine($"  Cards    : {cards.Count}/{totalCards} extracted ({100.0 * cards.Count / Math.Max(1, totalCards):F1}%)");
        Console.WriteLine($"  Potions  : {potions.Count}/{totalPotions} extracted ({100.0 * potions.Count / Math.Max(1, totalPotions):F1}%)");
        Console.WriteLine($"  Monsters : {monsters.Count}/{totalMonsters} extracted ({100.0 * monsters.Count / Math.Max(1, totalMonsters):F1}%)");
        Console.WriteLine($"  Audit    : {auditPath}");
        Console.WriteLine($"  Card manifest: {cardAuditPath}");
        return 0;
    }

    private static string FindRepoRoot(string start)
    {
        string? cur = start;
        while (cur != null)
        {
            if (File.Exists(Path.Combine(cur, "lakefile.toml")))
                return cur;
            cur = Directory.GetParent(cur)?.FullName;
        }
        return start;
    }

    // =========================================================================
    // Pass 1: Powers & Cards Metadata
    // =========================================================================
    private static Dictionary<string, PowerMeta> LoadPowerMetadata(string powersDir)
    {
        var result = new Dictionary<string, PowerMeta>(StringComparer.Ordinal);
        foreach (string path in Directory.GetFiles(powersDir, "*.cs").OrderBy(p => p, StringComparer.Ordinal))
        {
            var tree = CSharpSyntaxTree.ParseText(File.ReadAllText(path));
            var root = tree.GetCompilationUnitRoot();
            var cls = root.DescendantNodes().OfType<ClassDeclarationSyntax>().FirstOrDefault();
            if (cls == null || cls.Modifiers.Any(SyntaxKind.AbstractKeyword)) continue;

            string clsName = cls.Identifier.Text;
            string entryId = Slugify(clsName);
            string pType = "buff";
            string sType = "counter";
            string iType = "none";
            bool allowNeg = false;

            foreach (var prop in cls.Members.OfType<PropertyDeclarationSyntax>())
            {
                string propName = prop.Identifier.Text;
                string body = prop.ExpressionBody?.Expression.ToString() ?? prop.AccessorList?.ToString() ?? "";
                if (propName == "Type")
                {
                    if (body.Contains("PowerType.Debuff", StringComparison.Ordinal)) pType = "debuff";
                    else if (body.Contains("PowerType.None", StringComparison.Ordinal)) pType = "none";
                    else pType = "buff";
                }
                else if (propName == "StackType")
                {
                    if (body.Contains("PowerStackType.Single", StringComparison.Ordinal)) sType = "single";
                    else if (body.Contains("PowerStackType.None", StringComparison.Ordinal)) sType = "none";
                    else sType = "counter";
                }
                else if (propName == "Instanced")
                {
                    if (body.Contains("PowerInstanceType.InstancedPerApplier", StringComparison.Ordinal)) iType = "instancedPerApplier";
                    else if (body.Contains("PowerInstanceType.Instanced", StringComparison.Ordinal)) iType = "instanced";
                }
                else if (propName == "AllowNegative")
                {
                    if (body.Contains("true", StringComparison.Ordinal)) allowNeg = true;
                }
            }

            result[clsName] = new PowerMeta(clsName, entryId, pType, sType, iType, allowNeg);
        }
        return result;
    }

    private static Dictionary<string, CardMeta> LoadCardMetadata(string cardsDir)
    {
        var result = new Dictionary<string, CardMeta>(StringComparer.Ordinal);
        foreach (string path in Directory.GetFiles(cardsDir, "*.cs").OrderBy(p => p, StringComparer.Ordinal))
        {
            var tree = CSharpSyntaxTree.ParseText(File.ReadAllText(path));
            var root = tree.GetCompilationUnitRoot();
            var cls = root.DescendantNodes().OfType<ClassDeclarationSyntax>().FirstOrDefault();
            if (cls == null || cls.Modifiers.Any(SyntaxKind.AbstractKeyword)) continue;
            string clsName = cls.Identifier.Text;
            string entryId = Slugify(clsName);
            string cardType = "skill";
            int baseCost = 1;
            string rarity = "";
            string targetType = "";
            var ctor = cls.Members.OfType<ConstructorDeclarationSyntax>().FirstOrDefault(c => c.Initializer != null);
            if (ctor?.Initializer != null)
            {
                var args = ctor.Initializer.ArgumentList.Arguments;
                if (args.Count >= 2)
                {
                    if (TryEvalIntLiteral(args[0].Expression, out int cVal))
                        baseCost = cVal;
                    string ctStr = args[1].Expression.ToString();
                    if (ctStr.Contains("CardType.Attack", StringComparison.Ordinal)) cardType = "attack";
                    else if (ctStr.Contains("CardType.Power", StringComparison.Ordinal)) cardType = "power";
                    else if (ctStr.Contains("CardType.Status", StringComparison.Ordinal)) cardType = "status";
                    else if (ctStr.Contains("CardType.Curse", StringComparison.Ordinal)) cardType = "curse";
                    else if (ctStr.Contains("CardType.Quest", StringComparison.Ordinal)) cardType = "quest";
                    else cardType = "skill";
                }
                if (args.Count >= 4)
                {
                    rarity = ReadEnumMember(args[2].Expression, "CardRarity");
                    targetType = ReadEnumMember(args[3].Expression, "TargetType");
                }
            }
            var properties = cls.Members.OfType<PropertyDeclarationSyntax>().ToDictionary(p => p.Identifier.Text);
            bool costsX = properties.TryGetValue("HasEnergyCostX", out var xCost) &&
                xCost.ExpressionBody?.Expression.IsKind(SyntaxKind.TrueLiteralExpression) == true;
            int starCost = properties.TryGetValue("CanonicalStarCost", out var star) &&
                star.ExpressionBody?.Expression is { } starExpr && TryEvalIntLiteral(starExpr, out int starValue) ? starValue : 0;
            string[] ReadEnumList(string property, string enumType) =>
                properties.TryGetValue(property, out var declaration)
                    ? declaration.DescendantNodes().OfType<MemberAccessExpressionSyntax>()
                        .Select(m => ReadEnumMember(m, enumType)).Where(name => name != "").Distinct(StringComparer.Ordinal).ToArray()
                    : Array.Empty<string>();
            result[clsName] = new CardMeta(clsName, entryId, cardType, baseCost, rarity, targetType, costsX, starCost,
                ReadEnumList("CanonicalKeywords", "CardKeyword"), ReadEnumList("CanonicalTags", "CardTag"));
        }
        return result;
    }

    private static string ReadEnumMember(ExpressionSyntax expression, string enumType) =>
        expression is MemberAccessExpressionSyntax { Expression: IdentifierNameSyntax owner, Name: IdentifierNameSyntax name } &&
        owner.Identifier.ValueText == enumType ? name.Identifier.ValueText : "";

    // =========================================================================
    // Pass 2: Cards Extraction
    // =========================================================================
    private static List<ExtractedCard> ExtractCards(
        string cardsDir,
        Dictionary<string, PowerMeta> powers,
        Dictionary<string, CardMeta> cardMetas,
        List<SkipRecord> skips)
    {
        var extracted = new List<ExtractedCard>();
        foreach (string path in Directory.GetFiles(cardsDir, "*.cs").OrderBy(p => p, StringComparer.Ordinal))
        {
            string fileName = Path.GetFileName(path);
            var tree = CSharpSyntaxTree.ParseText(File.ReadAllText(path));
            var root = tree.GetCompilationUnitRoot();
            var cls = root.DescendantNodes().OfType<ClassDeclarationSyntax>().FirstOrDefault();
            if (cls == null || cls.Modifiers.Any(SyntaxKind.AbstractKeyword)) continue;

            string clsName = cls.Identifier.Text;
            string entryId = Slugify(clsName);

            var meta = cardMetas[clsName];
            void Skip(string reason, string detail, SyntaxNode location) =>
                skips.Add(new SkipRecord("Card", fileName, entryId, reason, detail, location.GetLocation().GetLineSpan().StartLinePosition));

            var xCost = cls.Members.OfType<PropertyDeclarationSyntax>()
                .FirstOrDefault(p => p.Identifier.Text == "HasEnergyCostX" && p.ToString().Contains("true", StringComparison.Ordinal));
            if (xCost != null)
            {
                Skip("x_cost_card", "HasEnergyCostX => true", xCost);
                continue;
            }

            var hookOverride = cls.Members.OfType<MethodDeclarationSyntax>()
                .FirstOrDefault(m => m.Modifiers.Any(SyntaxKind.OverrideKeyword) && !AllowedCardNonHookMethods.Contains(m.Identifier.Text));
            if (hookOverride != null)
            {
                Skip("custom_card_hook_override", $"overrides {hookOverride.Identifier.Text}", hookOverride);
                continue;
            }

            var onPlay = cls.Members.OfType<MethodDeclarationSyntax>().FirstOrDefault(m => m.Identifier.Text == "OnPlay");
            if (onPlay == null || onPlay.Body == null)
            {
                Skip("no_onplay_override", "No OnPlay body", (SyntaxNode?)onPlay ?? cls);
                continue;
            }

            var constStrings = CollectConstStrings(cls);
            var constNumbers = CollectConstNumbers(cls);
            if (!TryParseCanonicalVars(cls, constStrings, constNumbers, out var baseVars, out string varErr, out var varLocation))
            {
                Skip("unsupported_dynamic_var", varErr, varLocation);
                continue;
            }

            // Keep only canonical dictionary keys; property accesses are resolved to those
            // keys before lookup. Each variant therefore has one independent value per var.
            var upgVars = baseVars.ToDictionary(kv => kv.Key, kv => kv.Value.Clone(), StringComparer.Ordinal);
            var onUpgrade = cls.Members.OfType<MethodDeclarationSyntax>().FirstOrDefault(m => m.Identifier.Text == "OnUpgrade");
            if (!TryApplyOnUpgrade(onUpgrade, meta, constStrings, constNumbers, upgVars, out var upgrade, out string upgErr, out var upgLocation))
            {
                Skip("unsupported_upgrade_statement", upgErr, upgLocation ?? cls);
                continue;
            }

            var ctxBase = new WalkerContext(powers, cardMetas, baseVars, constStrings, constNumbers, isCard: true, isPotion: false, isMonster: false);
            if (!TryWalkBlock(onPlay.Body, ctxBase, out var baseOps, out string walkErr, out string walkCat))
            {
                Skip(walkCat, walkErr, ctxBase.FailureNode ?? onPlay);
                continue;
            }

            var ctxUpg = new WalkerContext(powers, cardMetas, upgVars, constStrings, constNumbers, isCard: true, isPotion: false, isMonster: false);
            if (!TryWalkBlock(onPlay.Body, ctxUpg, out var upgOps, out string upgWalkErr, out string upgWalkCat))
            {
                Skip(upgWalkCat, upgWalkErr, ctxUpg.FailureNode ?? onPlay);
                continue;
            }

            if (baseOps.Count == 0 && upgOps.Count == 0)
            {
                Skip("empty_effect_program", "No EffectOps emitted", onPlay);
                continue;
            }

            extracted.Add(new ExtractedCard(entryId, clsName, fileName, upgrade, baseOps, upgOps));
        }
        return extracted;
    }

    // =========================================================================
    // Pass 3: Potions Extraction
    // =========================================================================
    private static List<ExtractedPotion> ExtractPotions(
        string potionsDir,
        Dictionary<string, PowerMeta> powers,
        Dictionary<string, CardMeta> cardMetas,
        List<SkipRecord> skips)
    {
        var extracted = new List<ExtractedPotion>();
        foreach (string path in Directory.GetFiles(potionsDir, "*.cs").OrderBy(p => p, StringComparer.Ordinal))
        {
            string fileName = Path.GetFileName(path);
            var tree = CSharpSyntaxTree.ParseText(File.ReadAllText(path));
            var root = tree.GetCompilationUnitRoot();
            var cls = root.DescendantNodes().OfType<ClassDeclarationSyntax>().FirstOrDefault();
            if (cls == null || cls.Modifiers.Any(SyntaxKind.AbstractKeyword)) continue;

            string clsName = cls.Identifier.Text;
            string entryId = Slugify(clsName);

            var usageProp = cls.Members.OfType<PropertyDeclarationSyntax>().FirstOrDefault(p => p.Identifier.Text == "Usage");
            string usageText = usageProp?.ToString() ?? "";
            if (usageText.Contains("PotionUsage.Automatic", StringComparison.Ordinal) ||
                usageText.Contains("PotionUsage.None", StringComparison.Ordinal))
            {
                skips.Add(new SkipRecord("Potion", fileName, entryId, "non_manual_potion_usage", usageText.Trim()));
                continue;
            }

            var hookOverride = cls.Members.OfType<MethodDeclarationSyntax>()
                .FirstOrDefault(m => m.Modifiers.Any(SyntaxKind.OverrideKeyword) && m.Identifier.Text != "OnUse");
            if (hookOverride != null)
            {
                skips.Add(new SkipRecord("Potion", fileName, entryId, "custom_potion_hook_override", $"overrides {hookOverride.Identifier.Text}"));
                continue;
            }

            var onUse = cls.Members.OfType<MethodDeclarationSyntax>().FirstOrDefault(m => m.Identifier.Text == "OnUse");
            if (onUse == null || onUse.Body == null)
            {
                skips.Add(new SkipRecord("Potion", fileName, entryId, "no_onuse_override", "No OnUse body"));
                continue;
            }

            var constStrings = CollectConstStrings(cls);
            var constNumbers = CollectConstNumbers(cls);
            if (!TryParseCanonicalVars(cls, constStrings, constNumbers, out var vars, out string varErr, out _))
            {
                skips.Add(new SkipRecord("Potion", fileName, entryId, "unsupported_dynamic_var", varErr));
                continue;
            }

            var targetProp = cls.Members.OfType<PropertyDeclarationSyntax>().FirstOrDefault(p => p.Identifier.Text == "TargetType");
            bool targetIsSelfOrAnyPlayer = targetProp != null &&
                (targetProp.ToString().Contains("TargetType.Self", StringComparison.Ordinal) ||
                 targetProp.ToString().Contains("TargetType.AnyPlayer", StringComparison.Ordinal));

            var ctx = new WalkerContext(powers, cardMetas, vars, constStrings, constNumbers,
                isCard: false, isPotion: true, isMonster: false, potionTargetSelfByDefault: targetIsSelfOrAnyPlayer);
            if (!TryWalkBlock(onUse.Body, ctx, out var ops, out string walkErr, out string walkCat))
            {
                skips.Add(new SkipRecord("Potion", fileName, entryId, walkCat, walkErr));
                continue;
            }
            if (ops.Count == 0)
            {
                skips.Add(new SkipRecord("Potion", fileName, entryId, "empty_effect_program", "No EffectOps emitted"));
                continue;
            }
            extracted.Add(new ExtractedPotion(entryId, clsName, ops));
        }
        return extracted;
    }

    // =========================================================================
    // Pass 4: Monsters Extraction
    // =========================================================================
    private static List<ExtractedMonster> ExtractMonsters(
        string monstersDir,
        Dictionary<string, PowerMeta> powers,
        List<SkipRecord> skips)
    {
        var extracted = new List<ExtractedMonster>();
        var emptyCards = new Dictionary<string, CardMeta>(StringComparer.Ordinal);
        foreach (string path in Directory.GetFiles(monstersDir, "*.cs").OrderBy(p => p, StringComparer.Ordinal))
        {
            string fileName = Path.GetFileName(path);
            var tree = CSharpSyntaxTree.ParseText(File.ReadAllText(path));
            var root = tree.GetCompilationUnitRoot();
            var cls = root.DescendantNodes().OfType<ClassDeclarationSyntax>().FirstOrDefault();
            if (cls == null || cls.Modifiers.Any(SyntaxKind.AbstractKeyword)) continue;

            string clsName = cls.Identifier.Text;
            string entryId = Slugify(clsName);

            var genSm = cls.Members.OfType<MethodDeclarationSyntax>()
                .FirstOrDefault(m => m.Identifier.Text == "GenerateMoveStateMachine");
            if (genSm == null || genSm.Body == null)
            {
                skips.Add(new SkipRecord("Monster", fileName, entryId, "no_move_state_machine", "No GenerateMoveStateMachine"));
                continue;
            }

            bool hookRejected = false;
            foreach (var m in cls.Members.OfType<MethodDeclarationSyntax>().Where(m => m.Modifiers.Any(SyntaxKind.OverrideKeyword)))
            {
                if (!AllowedMonsterNonHookMethods.Contains(m.Identifier.Text))
                {
                    skips.Add(new SkipRecord("Monster", fileName, entryId, "monster_lifecycle_hook", $"overrides {m.Identifier.Text}"));
                    hookRejected = true;
                    break;
                }
                if (m.Identifier.Text == "AfterAddedToRoom" && !IsTrivialBaseCallMethod(m))
                {
                    skips.Add(new SkipRecord("Monster", fileName, entryId, "monster_after_added_hook", "Non-trivial AfterAddedToRoom"));
                    hookRejected = true;
                    break;
                }
            }
            if (hookRejected) continue;

            string smText = genSm.Body.ToString();
            if (smText.Contains("ConditionalBranchState", StringComparison.Ordinal))
            {
                skips.Add(new SkipRecord("Monster", fileName, entryId, "conditional_branch_state", "Uses ConditionalBranchState"));
                continue;
            }

            var constStrings = CollectConstStrings(cls);
            var ascProps = CollectMonsterAscProps(cls);

            if (!TryParseMonsterStateMachine(genSm.Body, constStrings, out string initialId, out var nodes, out var moveMethodMap, out string smCat, out string smErr))
            {
                skips.Add(new SkipRecord("Monster", fileName, entryId, smCat, smErr));
                continue;
            }

            var methodMap = cls.Members.OfType<MethodDeclarationSyntax>()
                .GroupBy(m => m.Identifier.Text, StringComparer.Ordinal)
                .ToDictionary(g => g.Key, g => g.First(), StringComparer.Ordinal);

            var moves = new List<MonsterMoveSpec>();
            bool moveFailed = false;
            foreach (var (moveId, methodName) in moveMethodMap)
            {
                if (!methodMap.TryGetValue(methodName, out var methodDecl) || methodDecl.Body == null)
                {
                    skips.Add(new SkipRecord("Monster", fileName, entryId, "missing_move_method", $"Cannot find method {methodName}"));
                    moveFailed = true;
                    break;
                }
                var mCtx = new WalkerContext(powers, emptyCards, new Dictionary<string, DynamicVarEntry>(StringComparer.Ordinal),
                    constStrings, new Dictionary<string, decimal>(StringComparer.Ordinal),
                    isCard: false, isPotion: false, isMonster: true, monsterAscProps: ascProps);
                if (!TryWalkBlock(methodDecl.Body, mCtx, out var ops, out string err, out string cat))
                {
                    skips.Add(new SkipRecord("Monster", fileName, entryId, cat, $"{moveId}/{methodName}: {err}"));
                    moveFailed = true;
                    break;
                }
                moves.Add(new MonsterMoveSpec(moveId, ops));
            }
            if (moveFailed) continue;

            var nodeIdSet = nodes.Select(n => n.Id).ToHashSet(StringComparer.Ordinal);
            var moveIdSet = moves.Select(m => m.MoveId).ToHashSet(StringComparer.Ordinal);
            if (string.IsNullOrEmpty(initialId) || !nodeIdSet.Contains(initialId))
            {
                skips.Add(new SkipRecord("Monster", fileName, entryId, "invalid_initial_state", $"initial={initialId}"));
                continue;
            }
            bool wfOk = true;
            foreach (var n in nodes)
            {
                if (n.IsRandomBranch)
                {
                    if (n.RandomTargets.Count == 0 || n.RandomTargets.Any(rt => !nodeIdSet.Contains(rt.TargetId) || rt.Weight <= 0))
                    { wfOk = false; break; }
                }
                else
                {
                    if (!moveIdSet.Contains(n.Id) || (!string.IsNullOrEmpty(n.FollowUpId) && !nodeIdSet.Contains(n.FollowUpId)))
                    { wfOk = false; break; }
                }
            }
            if (!wfOk)
            {
                skips.Add(new SkipRecord("Monster", fileName, entryId, "malformed_state_machine", "Broken transition target or missing move"));
                continue;
            }

            extracted.Add(new ExtractedMonster(entryId, clsName, initialId, nodes, moves));
        }
        return extracted;
    }

    private static bool IsTrivialBaseCallMethod(MethodDeclarationSyntax m)
    {
        if (m.Body == null) return false;
        foreach (var stmt in m.Body.Statements)
        {
            string s = stmt.ToString().Trim();
            if (s.StartsWith("await base.", StringComparison.Ordinal) ||
                s.StartsWith("return base.", StringComparison.Ordinal) ||
                s.StartsWith("base.", StringComparison.Ordinal) ||
                IsIgnorableVisualStatement(stmt))
                continue;
            return false;
        }
        return true;
    }

    private static Dictionary<string, AscVal> CollectMonsterAscProps(ClassDeclarationSyntax cls)
    {
        var map = new Dictionary<string, AscVal>(StringComparer.Ordinal);
        foreach (var field in cls.Members.OfType<FieldDeclarationSyntax>())
        {
            foreach (var v in field.Declaration.Variables)
            {
                if (v.Initializer?.Value != null && TryEvalAscVal(v.Initializer.Value, map, out var av))
                    map[v.Identifier.Text] = av;
            }
        }
        foreach (var prop in cls.Members.OfType<PropertyDeclarationSyntax>())
        {
            ExpressionSyntax? expr = prop.ExpressionBody?.Expression;
            if (expr == null && prop.AccessorList != null)
            {
                var getter = prop.AccessorList.Accessors.FirstOrDefault(a => a.IsKind(SyntaxKind.GetAccessorDeclaration));
                if (getter?.ExpressionBody != null) expr = getter.ExpressionBody.Expression;
                else if (getter?.Body?.Statements.Count == 1 && getter.Body.Statements[0] is ReturnStatementSyntax ret)
                    expr = ret.Expression;
            }
            if (expr != null && TryEvalAscVal(expr, map, out var av))
                map[prop.Identifier.Text] = av;
        }
        return map;
    }

    private static bool TryEvalAscVal(ExpressionSyntax expr, Dictionary<string, AscVal> known, out AscVal val)
    {
        expr = UnwrapExpr(expr);
        if (TryEvalIntLiteral(expr, out int lit))
        {
            val = AscVal.Const(lit);
            return true;
        }
        if (expr is IdentifierNameSyntax id && known.TryGetValue(id.Identifier.Text, out var existing))
        {
            val = existing;
            return true;
        }
        if (expr is InvocationExpressionSyntax inv &&
            inv.Expression.ToString().EndsWith("GetValueIfAscension", StringComparison.Ordinal) &&
            inv.ArgumentList.Arguments.Count == 3)
        {
            string lvlTxt = inv.ArgumentList.Arguments[0].Expression.ToString();
            int dot = lvlTxt.LastIndexOf('.');
            string lvlName = dot >= 0 ? lvlTxt[(dot + 1)..] : lvlTxt;
            if (AscensionThresholds.TryGetValue(lvlName, out int thresh) &&
                TryEvalIntWithKnown(inv.ArgumentList.Arguments[1].Expression, known, out int ascV) &&
                TryEvalIntWithKnown(inv.ArgumentList.Arguments[2].Expression, known, out int baseV))
            {
                val = new AscVal(thresh, ascV, baseV);
                return true;
            }
        }
        val = AscVal.Const(0);
        return false;
    }

    private static bool TryEvalIntWithKnown(ExpressionSyntax expr, Dictionary<string, AscVal> known, out int result)
    {
        expr = UnwrapExpr(expr);
        if (TryEvalIntLiteral(expr, out result)) return true;
        if (expr is IdentifierNameSyntax id && known.TryGetValue(id.Identifier.Text, out var av) && av.IsConst)
        {
            result = av.BaseValue;
            return true;
        }
        result = 0;
        return false;
    }

    private sealed class SmNodeBuilder
    {
        public string VarName = "";
        public string Id = "";
        public string? MethodName;
        public string FollowUpVar = "";
        public bool IsRandomBranch;
        public bool MustPerformOnce;
        public List<(string TargetVar, int Weight)> Branches = new();
    }

    private static bool TryParseMonsterStateMachine(
        BlockSyntax body,
        Dictionary<string, string> constStrings,
        out string initialStateId,
        out List<MonsterNodeSpec> nodes,
        out List<(string MoveId, string MethodName)> moveMethods,
        out string skipCat,
        out string skipErr)
    {
        initialStateId = "";
        nodes = new List<MonsterNodeSpec>();
        moveMethods = new List<(string, string)>();
        skipCat = "unsupported_state_machine";
        skipErr = "";

        var byVar = new Dictionary<string, SmNodeBuilder>(StringComparer.Ordinal);
        string? initialVar = null;

        bool RegisterStateCreation(string varName, ObjectCreationExpressionSyntax obj, out string cat, out string err)
        {
            cat = "unsupported_state_machine";
            err = "";
            string tName = obj.Type.ToString();
            if (tName.EndsWith("MoveState", StringComparison.Ordinal))
            {
                var args = obj.ArgumentList?.Arguments ?? default;
                if (args.Count < 2) { err = "MoveState requires >= 2 args"; return false; }
                if (!TryEvalString(args[0].Expression, constStrings, out string stateId))
                { err = $"Non-constant MoveState id: {args[0]}"; return false; }
                string mName = ExtractMethodName(args[1].Expression);
                if (string.IsNullOrEmpty(mName))
                { err = $"Non-method-group MoveState callback: {args[1]}"; return false; }

                bool mustOnce = false;
                if (obj.Initializer != null)
                {
                    foreach (var initExpr in obj.Initializer.Expressions)
                    {
                        if (initExpr is AssignmentExpressionSyntax assign &&
                            assign.Left.ToString() == "MustPerformOnceBeforeTransitioning" &&
                            assign.Right.ToString() == "true")
                            mustOnce = true;
                    }
                }
                byVar[varName] = new SmNodeBuilder
                {
                    VarName = varName,
                    Id = stateId,
                    MethodName = mName,
                    MustPerformOnce = mustOnce
                };
                return true;
            }
            if (tName.EndsWith("RandomBranchState", StringComparison.Ordinal))
            {
                var args = obj.ArgumentList?.Arguments ?? default;
                if (args.Count < 1 || !TryEvalString(args[0].Expression, constStrings, out string stateId))
                { err = "RandomBranchState non-constant id"; return false; }
                byVar[varName] = new SmNodeBuilder
                {
                    VarName = varName,
                    Id = stateId,
                    IsRandomBranch = true
                };
                return true;
            }
            err = $"Unsupported state type: {tName}";
            return false;
        }

        bool ProcessValueExpr(ExpressionSyntax rawExpr, string? targetVarName, out string? resolvedVar, out string cat, out string err)
        {
            cat = "unsupported_state_machine";
            err = "";
            resolvedVar = null;
            var expr = UnwrapCastAndParen(rawExpr);

            if (expr is ObjectCreationExpressionSyntax obj)
            {
                string vn = targetVarName ?? $"__anon_{byVar.Count}";
                if (!RegisterStateCreation(vn, obj, out cat, out err)) return false;
                resolvedVar = vn;
                return true;
            }
            if (expr is IdentifierNameSyntax id)
            {
                resolvedVar = id.Identifier.Text;
                return true;
            }
            if (expr is AssignmentExpressionSyntax assign)
            {
                if (!ProcessValueExpr(assign.Right, targetVarName, out string? rhsVar, out cat, out err)) return false;
                if (rhsVar == null) { err = $"Failed to resolve RHS in {assign}"; return false; }
                if (assign.Left is MemberAccessExpressionSyntax ma &&
                    ma.Name.Identifier.Text == "FollowUpState" &&
                    ma.Expression is IdentifierNameSyntax ownerId)
                {
                    if (!byVar.TryGetValue(ownerId.Identifier.Text, out var ownerNode))
                    { err = $"Unknown FollowUpState owner {ownerId}"; return false; }
                    ownerNode.FollowUpVar = rhsVar;
                    resolvedVar = rhsVar;
                    return true;
                }
                if (assign.Left is IdentifierNameSyntax lhsId && byVar.TryGetValue(rhsVar, out var srcNode))
                {
                    byVar[lhsId.Identifier.Text] = srcNode;
                    resolvedVar = lhsId.Identifier.Text;
                    return true;
                }
                err = $"Unsupported chained assignment: {assign}";
                return false;
            }
            err = $"Unsupported state-machine expression: {rawExpr}";
            return false;
        }

        foreach (var stmt in body.Statements)
        {
            if (stmt is LocalDeclarationStatementSyntax localDecl)
            {
                foreach (var v in localDecl.Declaration.Variables)
                {
                    if (v.Initializer == null) continue;
                    string vn = v.Identifier.Text;
                    string initText = v.Initializer.Value.ToString();
                    if (initText.StartsWith("new List<MonsterState>", StringComparison.Ordinal))
                        continue;
                    if (!ProcessValueExpr(v.Initializer.Value, vn, out string? resolved, out skipCat, out skipErr))
                        return false;
                    if (resolved != null && resolved != vn && byVar.TryGetValue(resolved, out var nRef))
                        byVar[vn] = nRef;
                }
            }
            else if (stmt is ExpressionStatementSyntax exprStmt)
            {
                var expr = UnwrapCastAndParen(exprStmt.Expression);
                if (expr is AssignmentExpressionSyntax assign)
                {
                    if (assign.Left is MemberAccessExpressionSyntax ma && ma.Expression is IdentifierNameSyntax ownerId)
                    {
                        string prop = ma.Name.Identifier.Text;
                        if (!byVar.TryGetValue(ownerId.Identifier.Text, out var ownerNode))
                        { skipErr = $"Unknown node var {ownerId}"; return false; }
                        if (prop == "FollowUpState")
                        {
                            if (!ProcessValueExpr(assign.Right, null, out string? rhsVar, out skipCat, out skipErr) || rhsVar == null)
                                return false;
                            ownerNode.FollowUpVar = rhsVar;
                        }
                        else if (prop == "MustPerformOnceBeforeTransitioning")
                        {
                            ownerNode.MustPerformOnce = assign.Right.ToString().Trim() == "true";
                        }
                        else
                        {
                            skipErr = $"Unsupported state property assignment: {exprStmt}";
                            return false;
                        }
                    }
                    else
                    {
                        skipErr = $"Unsupported assignment: {exprStmt}";
                        return false;
                    }
                }
                else if (expr is InvocationExpressionSyntax inv && inv.Expression is MemberAccessExpressionSyntax ma)
                {
                    string method = ma.Name.Identifier.Text;
                    if (method == "Add") continue;
                    if (method == "AddBranch" && ma.Expression is IdentifierNameSyntax rbId && byVar.TryGetValue(rbId.Identifier.Text, out var rbNode) && rbNode.IsRandomBranch)
                    {
                        if (!TryParseRandomAddBranch(inv, out string targetVar, out int weight, out skipCat, out skipErr))
                            return false;
                        rbNode.Branches.Add((targetVar, weight));
                    }
                    else
                    {
                        skipErr = $"Unsupported invocation in GenerateMoveStateMachine: {exprStmt}";
                        return false;
                    }
                }
                else
                {
                    skipErr = $"Unsupported statement in GenerateMoveStateMachine: {exprStmt}";
                    return false;
                }
            }
            else if (stmt is ReturnStatementSyntax ret && ret.Expression != null)
            {
                var retExpr = UnwrapCastAndParen(ret.Expression);
                if (retExpr is ObjectCreationExpressionSyntax obj &&
                    obj.Type.ToString().EndsWith("MonsterMoveStateMachine", StringComparison.Ordinal) &&
                    obj.ArgumentList != null && obj.ArgumentList.Arguments.Count >= 2)
                {
                    var arg1 = UnwrapCastAndParen(obj.ArgumentList.Arguments[1].Expression);
                    if (arg1 is IdentifierNameSyntax initId)
                        initialVar = initId.Identifier.Text;
                    else
                    {
                        skipErr = $"Non-identifier initial state: {arg1}";
                        return false;
                    }
                }
                else
                {
                    skipErr = $"Unsupported return in GenerateMoveStateMachine: {ret}";
                    return false;
                }
            }
            else
            {
                skipCat = "unsupported_state_machine_control_flow";
                skipErr = $"Unsupported control flow ({stmt.Kind()}) in GenerateMoveStateMachine";
                return false;
            }
        }

        if (initialVar == null || !byVar.TryGetValue(initialVar, out var initBuilder))
        {
            skipErr = "Missing initial state in return statement";
            return false;
        }
        initialStateId = initBuilder.Id;

        var seenIds = new HashSet<string>(StringComparer.Ordinal);
        foreach (var b in byVar.Values)
        {
            if (!seenIds.Add(b.Id)) continue;
            if (b.IsRandomBranch)
            {
                var targets = new List<(string, int)>();
                foreach (var (tv, w) in b.Branches)
                {
                    if (!byVar.TryGetValue(tv, out var tn))
                    { skipErr = $"Unknown branch target var {tv}"; return false; }
                    targets.Add((tn.Id, w));
                }
                nodes.Add(new MonsterNodeSpec(b.Id, "", true, targets, false));
            }
            else
            {
                string followUpId = "";
                if (!string.IsNullOrEmpty(b.FollowUpVar))
                {
                    if (!byVar.TryGetValue(b.FollowUpVar, out var fn))
                    { skipErr = $"Unknown follow-up var {b.FollowUpVar}"; return false; }
                    followUpId = fn.Id;
                }
                nodes.Add(new MonsterNodeSpec(b.Id, followUpId, false, new List<(string, int)>(), b.MustPerformOnce));
                moveMethods.Add((b.Id, b.MethodName ?? ""));
            }
        }
        return true;
    }

    private static bool TryParseRandomAddBranch(
        InvocationExpressionSyntax inv,
        out string targetVar,
        out int weight,
        out string cat,
        out string err)
    {
        targetVar = "";
        weight = 1;
        cat = "random_branch_repeat_or_cooldown";
        err = "";
        var args = inv.ArgumentList.Arguments;
        if (args.Count < 2)
        {
            err = $"Unexpected AddBranch arity {args.Count}";
            return false;
        }
        if (UnwrapCastAndParen(args[0].Expression) is not IdentifierNameSyntax tid)
        {
            err = $"Non-identifier branch target: {args[0]}";
            return false;
        }
        targetVar = tid.Identifier.Text;

        bool hasCanRepeatForever = false;
        decimal? weightVal = null;
        for (int i = 1; i < args.Count; i++)
        {
            var e = UnwrapExpr(args[i].Expression);
            string s = e.ToString();
            if (s.Contains("MoveRepeatType.", StringComparison.Ordinal))
            {
                if (s.EndsWith("MoveRepeatType.CanRepeatForever", StringComparison.Ordinal))
                    hasCanRepeatForever = true;
                else
                {
                    err = $"Unsupported repeat constraint {s}";
                    return false;
                }
            }
            else if (e is ParenthesizedLambdaExpressionSyntax lam)
            {
                if (lam.ExpressionBody != null && TryEvalDecimalLiteral(lam.ExpressionBody, out decimal wLam))
                    weightVal = wLam;
                else
                {
                    err = $"Dynamic weight lambda: {lam}";
                    return false;
                }
            }
            else if (TryEvalDecimalLiteral(e, out decimal numLit))
            {
                if (i == 1 && args.Count >= 3 && args[2].Expression.ToString().Contains("MoveRepeatType.", StringComparison.Ordinal))
                {
                    if (numLit != 0m)
                    {
                        err = $"Non-zero cooldown {numLit}";
                        return false;
                    }
                }
                else if (i == args.Count - 1 && hasCanRepeatForever)
                {
                    weightVal = numLit;
                }
                else
                {
                    err = $"Uses maxRepeats/cooldown overload: {inv}";
                    return false;
                }
            }
            else
            {
                err = $"Unsupported AddBranch arg: {e}";
                return false;
            }
        }
        if (!hasCanRepeatForever)
        {
            err = $"RandomBranch missing CanRepeatForever: {inv}";
            return false;
        }
        decimal wFinal = weightVal ?? 1m;
        if (wFinal <= 0m || wFinal != decimal.Truncate(wFinal))
        {
            err = $"Non-integer/non-positive weight {wFinal}";
            return false;
        }
        weight = (int)wFinal;
        return true;
    }

    // =========================================================================
    // DynamicVars & OnUpgrade Parser
    // =========================================================================
    private static Dictionary<string, string> CollectConstStrings(ClassDeclarationSyntax cls)
    {
        var map = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var f in cls.Members.OfType<FieldDeclarationSyntax>())
        {
            foreach (var v in f.Declaration.Variables)
            {
                if (v.Initializer?.Value is LiteralExpressionSyntax lit && lit.IsKind(SyntaxKind.StringLiteralExpression))
                    map[v.Identifier.Text] = lit.Token.ValueText;
            }
        }
        return map;
    }

    private static Dictionary<string, decimal> CollectConstNumbers(ClassDeclarationSyntax cls)
    {
        var map = new Dictionary<string, decimal>(StringComparer.Ordinal);
        foreach (var f in cls.Members.OfType<FieldDeclarationSyntax>())
        {
            foreach (var v in f.Declaration.Variables)
            {
                if (v.Initializer?.Value != null && TryEvalDecimalLiteral(v.Initializer.Value, out decimal d))
                    map[v.Identifier.Text] = d;
            }
        }
        foreach (var p in cls.Members.OfType<PropertyDeclarationSyntax>())
        {
            if (p.ExpressionBody?.Expression != null && TryEvalDecimalLiteral(p.ExpressionBody.Expression, out decimal d))
                map[p.Identifier.Text] = d;
        }
        return map;
    }

    private static bool TryParseCanonicalVars(
        ClassDeclarationSyntax cls,
        Dictionary<string, string> constStrings,
        Dictionary<string, decimal> constNumbers,
        out Dictionary<string, DynamicVarEntry> vars,
        out string err,
        out SyntaxNode location)
    {
        vars = new Dictionary<string, DynamicVarEntry>(StringComparer.Ordinal);
        err = "";
        var prop = cls.Members.OfType<PropertyDeclarationSyntax>().FirstOrDefault(p => p.Identifier.Text == "CanonicalVars");
        if (prop == null) { location = cls; return true; }
        location = prop;

        foreach (var obj in prop.DescendantNodes().OfType<ObjectCreationExpressionSyntax>())
        {
            string tRaw = obj.Type.ToString();
            if (tRaw.Contains("ReadOnly", StringComparison.Ordinal) || tRaw.StartsWith("List<", StringComparison.Ordinal))
                continue;
            location = obj;

            var args = obj.ArgumentList?.Arguments ?? default;
            if (tRaw is "CalculatedBlockVar" or "CalculatedDamageVar")
            {
                if (!TryParseCalculatedVar(obj, tRaw == "CalculatedDamageVar", out var calculated))
                {
                    err = $"Unsupported calculated variable or multiplier: {obj.Parent?.Parent ?? obj}";
                    return false;
                }
                vars[calculated.Key] = calculated;
            }
            else if (tRaw is "CalculationBaseVar" or "CalculationExtraVar" or "ExtraDamageVar")
            {
                if (!IsCanonicalVarElement(obj) || args.Count != 1 ||
                    !TryEvalDecimalExpr(args[0].Expression, constNumbers, out decimal value))
                {
                    err = $"Unsupported calculated component: {obj}";
                    return false;
                }
                string key = tRaw[..^3];
                vars[key] = new DynamicVarEntry { Key = key, Kind = tRaw, BaseValue = value };
            }
            else if (tRaw == "DamageVar" || tRaw == "OstyDamageVar")
            {
                if (tRaw == "OstyDamageVar") { err = "OstyDamageVar requires Osty HP scaling"; return false; }
                string key = "Damage";
                int valIdx = 0;
                if (args.Count >= 3 && TryEvalString(args[0].Expression, constStrings, out string customKey))
                {
                    key = customKey;
                    valIdx = 1;
                }
                if (args.Count <= valIdx || !TryEvalDecimalExpr(args[valIdx].Expression, constNumbers, out decimal dVal))
                { err = $"Cannot eval DamageVar value: {obj}"; return false; }
                var props = args.Count > valIdx + 1 ? args[valIdx + 1].Expression : null;
                var (unpow, unblk) = props == null ? (false, false) : ParseValuePropFlags(props);
                vars[key] = new DynamicVarEntry { Key = key, Kind = "Damage", BaseValue = dVal, Unpowered = unpow, Unblockable = unblk, DeclaredProps = props };
            }
            else if (tRaw == "BlockVar")
            {
                string key = "Block";
                int valIdx = 0;
                if (args.Count >= 3 && TryEvalString(args[0].Expression, constStrings, out string customKey))
                {
                    key = customKey;
                    valIdx = 1;
                }
                if (args.Count <= valIdx || !TryEvalDecimalExpr(args[valIdx].Expression, constNumbers, out decimal bVal))
                { err = $"Cannot eval BlockVar value: {obj}"; return false; }
                var (unpow, unblk) = args.Count > valIdx + 1 ? ParseValuePropFlags(args[valIdx + 1].Expression) : (false, false);
                vars[key] = new DynamicVarEntry { Key = key, Kind = "Block", BaseValue = bVal, Unpowered = unpow, Unblockable = unblk };
            }
            else if (obj.Type is GenericNameSyntax gName && gName.Identifier.Text == "PowerVar")
            {
                string powCls = gName.TypeArgumentList.Arguments[0].ToString();
                string key = powCls;
                int valIdx = 0;
                if (args.Count >= 2 && TryEvalString(args[0].Expression, constStrings, out string customKey))
                {
                    key = customKey;
                    valIdx = 1;
                }
                if (args.Count <= valIdx || !TryEvalDecimalExpr(args[valIdx].Expression, constNumbers, out decimal pVal))
                { err = $"Cannot eval PowerVar value: {obj}"; return false; }
                vars[key] = new DynamicVarEntry { Key = key, Kind = "Power", BaseValue = pVal };
            }
            else if (tRaw is "CardsVar" or "EnergyVar" or "StarsVar" or "RepeatVar" or "HitCountVar" or "HealVar" or "ForgeVar" or "SummonVar" or "HpLossVar" or "MaxHpVar" or "GoldVar")
            {
                string key = tRaw[..^3];
                int valIdx = 0;
                if (args.Count >= 2 && TryEvalString(args[0].Expression, constStrings, out string customKey))
                {
                    key = customKey;
                    valIdx = 1;
                }
                if (args.Count <= valIdx || !TryEvalDecimalExpr(args[valIdx].Expression, constNumbers, out decimal nVal))
                { err = $"Cannot eval {tRaw} value: {obj}"; return false; }
                vars[key] = new DynamicVarEntry { Key = key, Kind = tRaw, BaseValue = nVal };
            }
            else if (tRaw is "DynamicVar" or "IntVar")
            {
                if (args.Count >= 2 &&
                    TryEvalString(args[0].Expression, constStrings, out string key) &&
                    TryEvalDecimalExpr(args[1].Expression, constNumbers, out decimal nVal))
                {
                    vars[key] = new DynamicVarEntry { Key = key, Kind = tRaw, BaseValue = nVal };
                }
                else
                {
                    err = $"Cannot eval {tRaw}: {obj}";
                    return false;
                }
            }
            else
            {
                err = $"Unsupported DynamicVar subclass: {tRaw}";
                return false;
            }
        }
        return true;
    }

    private static bool IsCanonicalVarElement(ExpressionSyntax expr) => expr.Parent switch
    {
        InitializerExpressionSyntax i => i.IsKind(SyntaxKind.ArrayInitializerExpression),
        ArgumentSyntax { Parent.Parent: ObjectCreationExpressionSyntax wrapper } =>
            wrapper.Type is GenericNameSyntax g && g.Identifier.ValueText == "_003C_003Ez__ReadOnlySingleElementList",
        _ => false
    };

    private static bool TryParseCalculatedVar(ObjectCreationExpressionSyntax obj, bool isDamage, out DynamicVarEntry result)
    {
        result = null!;
        if (obj.ArgumentList is not { Arguments: [var propsArg] } || !TryParseDamageFlags(propsArg.Expression, out _) ||
            obj.Parent is not MemberAccessExpressionSyntax { Name: IdentifierNameSyntax { Identifier.ValueText: "WithMultiplier" } } access ||
            access.Parent is not InvocationExpressionSyntax invocation ||
            !IsCanonicalVarElement(invocation) ||
            invocation.ArgumentList.Arguments is not [var multiplier] ||
            !TryMatchCalculatedSource(multiplier.Expression, out var source) ||
            (isDamage && source != ValueSource.ActorBlock))
            return false;

        string key = isDamage ? "CalculatedDamage" : "CalculatedBlock";
        result = new DynamicVarEntry
        {
            Key = key,
            Kind = key,
            DeclaredProps = propsArg.Expression,
            CalculatedSource = source
        };
        return true;
    }

    private static bool TryMatchCalculatedSource(ExpressionSyntax expr, out ValueSource source)
    {
        source = default;
        if (StripParens(expr) is not ParenthesizedLambdaExpressionSyntax lambda ||
            lambda.ParameterList.Parameters is not [var card, var target] ||
            card.Type is not IdentifierNameSyntax { Identifier.ValueText: "CardModel" } ||
            target.Type is not NullableTypeSyntax { ElementType: IdentifierNameSyntax { Identifier.ValueText: "Creature" } } ||
            lambda.ExpressionBody is not { } body)
            return false;

        if (IsPath(body, [card.Identifier.ValueText, "Owner", "Creature", "Block"]))
        {
            source = ValueSource.ActorBlock;
            return true;
        }
        if (StripParens(body) is BinaryExpressionSyntax coalesce && coalesce.IsKind(SyntaxKind.CoalesceExpression) &&
            StripParens(coalesce.Left) is ConditionalAccessExpressionSyntax conditional &&
            IsPath(conditional.Expression, [target.Identifier.ValueText]) &&
            conditional.WhenNotNull is MemberBindingExpressionSyntax { Name: IdentifierNameSyntax { Identifier.ValueText: "Block" } } &&
            TryEvalIntLiteral(coalesce.Right, out int zero) && zero == 0)
        {
            source = ValueSource.ChosenBlock;
            return true;
        }
        if (StripParens(body) is InvocationExpressionSyntax count && IsPath(count.Expression, ["Enumerable", "Count"]) &&
            count.ArgumentList.Arguments is [var pile] && IsPileCards(pile.Expression, "Discard", [card.Identifier.ValueText, "Owner"]))
        {
            source = ValueSource.DiscardCount;
            return true;
        }
        return false;
    }

    private static bool TryApplyOnUpgrade(
        MethodDeclarationSyntax? onUpgrade,
        CardMeta meta,
        Dictionary<string, string> constStrings,
        Dictionary<string, decimal> constNumbers,
        Dictionary<string, DynamicVarEntry> vars,
        out CardUpgradeMeta upgrade,
        out string err,
        out SyntaxNode? location)
    {
        err = "";
        location = onUpgrade;
        upgrade = new CardUpgradeMeta(meta.BaseCost, meta.Keywords);
        if (onUpgrade == null) return true;
        if (onUpgrade.Body == null)
        {
            err = "Expected an OnUpgrade block";
            return false;
        }
        int cost = meta.BaseCost;
        var keywords = meta.Keywords.ToList();
        foreach (var stmt in onUpgrade.Body.Statements)
        {
            location = stmt;
            if (stmt is ExpressionStatementSyntax es && es.Expression is InvocationExpressionSyntax inv &&
                inv.ArgumentList.Arguments is [var arg])
            {
                if (IsPath(inv.Expression, ["AddKeyword"]) || IsPath(inv.Expression, ["this", "AddKeyword"]))
                {
                    string keyword = ReadEnumMember(arg.Expression, "CardKeyword");
                    if (keyword == "") { err = $"Unsupported keyword in OnUpgrade: {stmt}"; return false; }
                    if (!keywords.Contains(keyword)) keywords.Add(keyword);
                    continue;
                }
                if (IsPath(inv.Expression, ["RemoveKeyword"]) || IsPath(inv.Expression, ["this", "RemoveKeyword"]))
                {
                    string keyword = ReadEnumMember(arg.Expression, "CardKeyword");
                    if (keyword == "") { err = $"Unsupported keyword in OnUpgrade: {stmt}"; return false; }
                    keywords.Remove(keyword);
                    continue;
                }
                if ((IsPath(inv.Expression, ["EnergyCost", "UpgradeBy"]) || IsPath(inv.Expression, ["this", "EnergyCost", "UpgradeBy"])) &&
                    TryEvalDecimalExpr(arg.Expression, constNumbers, out decimal costDelta) &&
                    costDelta is >= int.MinValue and <= int.MaxValue && costDelta == decimal.Truncate(costDelta))
                {
                    if (costDelta != 0) cost = Math.Max(0, checked(cost + (int)costDelta));
                    continue;
                }
                if (inv.Expression is MemberAccessExpressionSyntax ma)
                {
                    string mName = ma.Name.Identifier.Text;
                    if (mName == "UpgradeValueBy")
                    {
                        if (!TryResolveDynamicVarKey(ma.Expression, constStrings, out string key))
                        { err = $"Cannot resolve DynamicVar key in OnUpgrade: {stmt}"; return false; }
                        if (!TryEvalDecimalExpr(inv.ArgumentList.Arguments[0].Expression, constNumbers, out decimal delta))
                        { err = $"Non-constant UpgradeValueBy delta: {stmt}"; return false; }
                        if (!vars.TryGetValue(key, out var dv))
                        { err = $"DynamicVar key '{key}' not found in CanonicalVars"; return false; }
                        if (dv.CalculatedSource != null)
                        { err = $"Upgrade calculated components, not the derived variable: {stmt}"; return false; }
                        dv.BaseValue += delta;
                        continue;
                    }
                }
            }
            err = $"Unsupported OnUpgrade statement: {stmt}";
            return false;
        }
        upgrade = new CardUpgradeMeta(cost, keywords.ToArray());
        return true;
    }

    // =========================================================================
    // Strict Zero-Silent-Drop Statement Walker (Cards, Potions, Monsters)
    // =========================================================================
    private sealed class WalkerContext
    {
        public Dictionary<string, PowerMeta> Powers { get; }
        public Dictionary<string, CardMeta> CardMetas { get; }
        public Dictionary<string, DynamicVarEntry> Vars { get; }
        public Dictionary<string, string> ConstStrings { get; }
        public Dictionary<string, decimal> ConstNumbers { get; }
        public Dictionary<string, AscVal> MonsterAscProps { get; }
        public bool IsCard { get; }
        public bool IsPotion { get; }
        public bool IsMonster { get; }
        public bool PotionTargetSelfByDefault { get; }

        public Dictionary<string, decimal> LocalNums { get; } = new(StringComparer.Ordinal);
        public Dictionary<string, AscVal> LocalAscs { get; } = new(StringComparer.Ordinal);
        public Dictionary<string, DynamicVarEntry> LocalVarAliases { get; } = new(StringComparer.Ordinal);
        public Dictionary<string, IrTarget> LocalTargets { get; } = new(StringComparer.Ordinal);
        public Dictionary<string, string> LocalCreatedCardClass { get; } = new(StringComparer.Ordinal);
        public Dictionary<string, (string CardClass, int Count)> LocalCreatedCardList { get; } = new(StringComparer.Ordinal);
        public Dictionary<string, (string ChoiceKind, int Count)> LocalSelectedCards { get; } = new(StringComparer.Ordinal);
        public int NextChoiceId { get; set; }
        public SyntaxNode? FailureNode { get; set; }

        public WalkerContext(
            Dictionary<string, PowerMeta> powers,
            Dictionary<string, CardMeta> cardMetas,
            Dictionary<string, DynamicVarEntry> vars,
            Dictionary<string, string> constStrings,
            Dictionary<string, decimal> constNumbers,
            bool isCard,
            bool isPotion,
            bool isMonster,
            bool potionTargetSelfByDefault = false,
            Dictionary<string, AscVal>? monsterAscProps = null)
        {
            Powers = powers;
            CardMetas = cardMetas;
            Vars = vars;
            ConstStrings = constStrings;
            ConstNumbers = constNumbers;
            IsCard = isCard;
            IsPotion = isPotion;
            IsMonster = isMonster;
            PotionTargetSelfByDefault = potionTargetSelfByDefault;
            MonsterAscProps = monsterAscProps ?? new Dictionary<string, AscVal>(StringComparer.Ordinal);
        }
    }

    private static bool TryWalkBlock(BlockSyntax block, WalkerContext ctx, out List<IrOp> ops, out string err, out string cat)
    {
        ops = new List<IrOp>();
        err = "";
        cat = "unsupported_statement";
        for (int i = 0; i < block.Statements.Count; i++)
        {
            var stmt = block.Statements[i];
            // An intervening command could change the tested power. Fold a snapshot
            // only into the immediately following attack.
            if (ctx.IsCard && TryMatchPowerHitCount(stmt, ctx, out var name, out var counts))
            {
                ctx.FailureNode = stmt;
                if (i + 1 < block.Statements.Count && block.Statements[i + 1] is ExpressionStatementSyntax following &&
                    UnwrapAwait(following.Expression) is InvocationExpressionSyntax attack &&
                    IsMember(attack.Expression, "Execute", out _))
                {
                    ctx.FailureNode = following;
                    if (TryWalkDamageCmdChain(attack, ctx, ops, out err, out cat, name, counts))
                    {
                        i++;
                        continue;
                    }
                    if (cat != "not_damage_cmd") return false;
                }
                cat = "unsupported_damage_cmd";
                err = $"Conditional hit count '{name}' must be used by the immediately following attack";
                return false;
            }
            if (!TryWalkStatement(stmt, ctx, ops, out err, out cat))
                return false;
        }
        return true;
    }

    private static bool TryWalkStatement(StatementSyntax stmt, WalkerContext ctx, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_statement";
        ctx.FailureNode = stmt;

        if (stmt is EmptyStatementSyntax) return true;
        if (IsIgnorableVisualStatement(stmt)) return true;

        if (stmt is BlockSyntax innerBlock)
        {
            foreach (var s in innerBlock.Statements)
            {
                if (!TryWalkStatement(s, ctx, ops, out err, out cat)) return false;
            }
            return true;
        }

        if (stmt is ReturnStatementSyntax ret)
        {
            if (ret.Expression == null || ret.Expression.ToString().Contains("Task.CompletedTask", StringComparison.Ordinal))
                return true;
            cat = "unsupported_return";
            err = $"Unsupported return: {ret}";
            return false;
        }

        if (stmt is LocalDeclarationStatementSyntax localDecl)
            return TryWalkLocalDecl(localDecl, ctx, ops, out err, out cat);

        if (stmt is ExpressionStatementSyntax exprStmt)
        {
            var e = UnwrapAwait(exprStmt.Expression);
            if (e is InvocationExpressionSyntax inv)
                return TryWalkInvocation(inv, ctx, ops, out err, out cat);
            cat = "unsupported_expression_statement";
            err = $"Unsupported expression statement: {exprStmt}";
            return false;
        }

        if (stmt is ForStatementSyntax forStmt)
            return TryWalkForLoop(forStmt, ctx, ops, out err, out cat);

        if (stmt is ForEachStatementSyntax forEach)
            return TryWalkForEach(forEach, ctx, ops, out err, out cat);

        if (stmt is IfStatementSyntax ifStmt)
            return TryWalkIf(ifStmt, ctx, ops, out err, out cat);

        cat = "unsupported_control_flow";
        err = $"Unsupported statement kind {stmt.Kind()}: {stmt.ToString().Split('\n')[0]}";
        return false;
    }

    private static bool TryWalkLocalDecl(LocalDeclarationStatementSyntax decl, WalkerContext ctx, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_local_declaration";
        foreach (var v in decl.Declaration.Variables)
        {
            string vn = v.Identifier.Text;
            if (v.Initializer == null)
            {
                err = $"Uninitialized local {vn}";
                return false;
            }
            var rawVal = UnwrapAwait(v.Initializer.Value);
            string rawText = rawVal.ToString();

            if (IsVisualExpression(rawVal))
                continue;

            if (TryResolveDynamicVarKey(rawVal, ctx.ConstStrings, out string dvKey) && ctx.Vars.TryGetValue(dvKey, out var dvEntry))
            {
                ctx.LocalVarAliases[vn] = dvEntry;
                continue;
            }

            if (TryResolveTarget(rawVal, ctx, out IrTarget tgt))
            {
                ctx.LocalTargets[vn] = tgt;
                continue;
            }

            if (ctx.IsMonster && TryResolveMonsterAscVal(rawVal, ctx, out var av))
            {
                ctx.LocalAscs[vn] = av;
                continue;
            }
            if (!ctx.IsMonster && TryResolveNumeric(rawVal, ctx, out decimal numVal))
            {
                ctx.LocalNums[vn] = numVal;
                continue;
            }

            if (TryMatchCreateCard(rawVal, out string createdCls))
            {
                ctx.LocalCreatedCardClass[vn] = createdCls;
                continue;
            }

            if (TryMatchCardSelect(rawVal, ctx, out string selKind, out int selCount))
            {
                ctx.LocalSelectedCards[vn] = (selKind, selCount);
                continue;
            }

            if (rawText.StartsWith("new List<CardModel>", StringComparison.Ordinal))
            {
                ctx.LocalCreatedCardList[vn] = ("", 0);
                continue;
            }

            if (rawVal is InvocationExpressionSyntax inv && TryWalkInvocation(inv, ctx, ops, out err, out cat))
                continue;

            err = $"Unsupported local variable initializer `{vn} = {rawText}`";
            return false;
        }
        return true;
    }

    private static bool TryWalkForLoop(ForStatementSyntax forStmt, WalkerContext ctx, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_for_loop";
        if (forStmt.Declaration == null || forStmt.Declaration.Variables.Count != 1)
        { err = "Non-standard for-loop init"; return false; }
        var iv = forStmt.Declaration.Variables[0];
        if (iv.Initializer == null || !TryEvalIntLiteral(iv.Initializer.Value, out int start) || start != 0)
        { err = "For-loop does not start at 0"; return false; }
        if (forStmt.Condition is not BinaryExpressionSyntax bin || !bin.IsKind(SyntaxKind.LessThanExpression) ||
            bin.Left.ToString() != iv.Identifier.Text)
        { err = $"Unsupported for-loop condition: {forStmt.Condition}"; return false; }
        if (forStmt.Incrementors.Count != 1 ||
            !(forStmt.Incrementors[0] is PostfixUnaryExpressionSyntax pu && pu.IsKind(SyntaxKind.PostIncrementExpression)))
        { err = "Unsupported for-loop incrementor"; return false; }

        int bound;
        if (ctx.IsMonster)
        {
            if (!TryResolveMonsterAscVal(bin.Right, ctx, out var av) || !av.IsConst)
            { err = $"Non-constant monster for-loop bound: {bin.Right}"; return false; }
            bound = av.BaseValue;
        }
        else
        {
            if (!TryResolveNumeric(bin.Right, ctx, out decimal dBound) || dBound != decimal.Truncate(dBound))
            { err = $"Non-constant for-loop bound: {bin.Right}"; return false; }
            bound = (int)dBound;
        }
        if (bound < 0 || bound > 12)
        { err = $"For-loop bound out of unroll range [0..12]: {bound}"; return false; }

        for (int i = 0; i < bound; i++)
        {
            if (!TryWalkStatement(forStmt.Statement, ctx, ops, out err, out cat))
                return false;
        }
        return true;
    }

    private static bool TryWalkForEach(ForEachStatementSyntax fe, WalkerContext ctx, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_foreach";
        if (IsVisualBlockOrStmt(fe.Statement))
            return true;

        if (TryResolveTarget(fe.Expression, ctx, out IrTarget collTarget) &&
            (collTarget == IrTarget.AllEnemies || collTarget == IrTarget.AllAllies))
        {
            string iterVar = fe.Identifier.Text;
            bool hadPrev = ctx.LocalTargets.TryGetValue(iterVar, out var prevTarget);
            ctx.LocalTargets[iterVar] = collTarget;
            bool ok = TryWalkStatement(fe.Statement, ctx, ops, out err, out cat);
            if (hadPrev) ctx.LocalTargets[iterVar] = prevTarget;
            else ctx.LocalTargets.Remove(iterVar);
            return ok;
        }

        if (fe.Expression is IdentifierNameSyntax selId && ctx.LocalSelectedCards.TryGetValue(selId.Identifier.Text, out var selInfo))
        {
            string iterVar = fe.Identifier.Text;
            var bodyStmts = fe.Statement is BlockSyntax b ? b.Statements.ToList() : new List<StatementSyntax> { fe.Statement };
            var nonVis = bodyStmts.Where(s => !IsIgnorableVisualStatement(s)).ToList();
            if (nonVis.Count == 1 && nonVis[0] is ExpressionStatementSyntax es &&
                UnwrapAwait(es.Expression) is InvocationExpressionSyntax inv &&
                inv.Expression is MemberAccessExpressionSyntax ma)
            {
                string full = ma.ToString();
                if (full == "CardCmd.Discard" && inv.ArgumentList.Arguments.Any(a => a.Expression.ToString() == iterVar))
                {
                    ops.Add(new OpDiscardChosen(ctx.NextChoiceId++, selInfo.Count));
                    return true;
                }
                if (full == "CardCmd.Exhaust" && inv.ArgumentList.Arguments.Any(a => a.Expression.ToString() == iterVar))
                {
                    ops.Add(new OpExhaustChosen(ctx.NextChoiceId++, selInfo.Count));
                    return true;
                }
            }
        }

        err = $"Unsupported foreach over {fe.Expression}";
        return false;
    }

    private static bool TryWalkIf(IfStatementSyntax ifStmt, WalkerContext ctx, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "conditional_branch_in_body";
        if (ifStmt.Else == null &&
            ifStmt.Condition is BinaryExpressionSyntax bin &&
            bin.IsKind(SyntaxKind.NotEqualsExpression) &&
            bin.Right.IsKind(SyntaxKind.NullLiteralExpression) &&
            bin.Left is IdentifierNameSyntax id &&
            ctx.LocalSelectedCards.TryGetValue(id.Identifier.Text, out var selInfo))
        {
            var bodyStmts = ifStmt.Statement is BlockSyntax b ? b.Statements.ToList() : new List<StatementSyntax> { ifStmt.Statement };
            var nonVis = bodyStmts.Where(s => !IsIgnorableVisualStatement(s)).ToList();
            if (nonVis.Count == 1 && nonVis[0] is ExpressionStatementSyntax es &&
                UnwrapAwait(es.Expression) is InvocationExpressionSyntax inv &&
                inv.Expression is MemberAccessExpressionSyntax ma)
            {
                string full = ma.ToString();
                if (full == "CardCmd.Discard")
                {
                    ops.Add(new OpDiscardChosen(ctx.NextChoiceId++, selInfo.Count));
                    return true;
                }
                if (full == "CardCmd.Exhaust")
                {
                    ops.Add(new OpExhaustChosen(ctx.NextChoiceId++, selInfo.Count));
                    return true;
                }
            }
        }
        if (ctx.IsCard && ifStmt.Else == null &&
            (ifStmt.Statement is BlockSyntax { Statements: [ExpressionStatementSyntax action] } ? action :
                ifStmt.Statement as ExpressionStatementSyntax) is { } actionStmt &&
            UnwrapAwait(actionStmt.Expression) is InvocationExpressionSyntax invocation &&
            TryMatchConditionalOp(ifStmt.Condition, invocation, ctx, out var conditionalOp))
        {
            ops.Add(conditionalOp);
            return true;
        }
        if (ifStmt.Else == null && IsVisualBlockOrStmt(ifStmt.Statement))
            return true;

        err = $"Conditional branch in body: if ({ifStmt.Condition})";
        return false;
    }

    private static bool TryMatchConditionalOp(ExpressionSyntax condition, InvocationExpressionSyntax action, WalkerContext ctx, out IrOp op)
    {
        op = null!;
        var args = action.ArgumentList.Arguments;
        if (HasNamedArguments(args)) return false;
        if (TryMatchPowerTest(condition, ctx, out var target, out var power, out bool negated) && !negated &&
            action.Expression is MemberAccessExpressionSyntax
            {
                Expression: IdentifierNameSyntax { Identifier.ValueText: "PowerCmd" },
                Name: GenericNameSyntax { Identifier.ValueText: "Apply", TypeArgumentList.Arguments: [IdentifierNameSyntax powerType] }
            } &&
            powerType.Identifier.ValueText == power.ClassName &&
            args is [var choice, var recipient, var amount, var applier, var card] &&
            IsPath(choice.Expression, ["choiceContext"]) &&
            TryMatchPowerRecipient(recipient.Expression, out var appliedTarget) && appliedTarget == target &&
            IsPath(applier.Expression, ["Owner", "Creature"]) && IsPath(card.Expression, ["this"]) &&
            TryResolveNumeric(amount.Expression, ctx, out decimal powerAmount))
        {
            op = new OpApplyPowerIfPresent(target, power, powerAmount);
            return true;
        }
        int count = 1;
        if (IsNoAttacksInHand(condition) && IsPath(action.Expression, ["CardPileCmd", "Draw"]) &&
            args.Count is 2 or 3 && IsPath(args[0].Expression, ["choiceContext"]) &&
            IsPath(args[^1].Expression, ["Owner"]) &&
            (args.Count == 2 || TryResolveInt(args[1].Expression, ctx, 0, out count)))
        {
            op = new OpDrawIfNoAttacks(count);
            return true;
        }
        return false;
    }

    private static bool TryMatchPowerRecipient(ExpressionSyntax expr, out IrTarget target)
    {
        target = IrTarget.Self;
        if (IsPath(expr, ["Owner", "Creature"])) return true;
        target = IrTarget.ChosenTarget;
        return IsPath(expr, ["cardPlay", "Target"]);
    }

    private static bool TryMatchPowerTest(ExpressionSyntax expr, WalkerContext ctx, out IrTarget target, out PowerMeta power, out bool negated)
    {
        expr = StripParens(expr);
        negated = expr is PrefixUnaryExpressionSyntax prefix && prefix.IsKind(SyntaxKind.LogicalNotExpression);
        if (negated) expr = StripParens(((PrefixUnaryExpressionSyntax)expr).Operand);
        power = null!;
        target = default;
        return expr is InvocationExpressionSyntax
        {
            Expression: MemberAccessExpressionSyntax
            {
                Name: GenericNameSyntax { Identifier.ValueText: "HasPower", TypeArgumentList.Arguments: [IdentifierNameSyntax powerType] }
            } test,
            ArgumentList.Arguments: []
        } && TryMatchPowerRecipient(test.Expression, out target) && ctx.Powers.TryGetValue(powerType.Identifier.ValueText, out power!);
    }

    private static bool TryMatchPowerHitCount(StatementSyntax stmt, WalkerContext ctx, out string name, out PowerHitCount result)
    {
        name = "";
        result = default;
        if (stmt is not LocalDeclarationStatementSyntax
            {
                Declaration:
                {
                    Type: PredefinedTypeSyntax type,
                    Variables: [VariableDeclaratorSyntax { Initializer.Value: { } value } local]
                }
            } || !type.Keyword.IsKind(SyntaxKind.IntKeyword) ||
            StripParens(value) is not ConditionalExpressionSyntax conditional ||
            !TryMatchPowerTest(conditional.Condition, ctx, out var target, out var power, out bool negated) ||
            !TryResolveInt(conditional.WhenTrue, ctx, 1, out int onTrue) ||
            !TryResolveInt(conditional.WhenFalse, ctx, 1, out int onFalse))
            return false;
        name = local.Identifier.ValueText;
        result = negated ? new(target, power, onFalse, onTrue) : new(target, power, onTrue, onFalse);
        return true;
    }

    private static bool IsNoAttacksInHand(ExpressionSyntax expr)
    {
        if (StripParens(expr) is not PrefixUnaryExpressionSyntax negation || !negation.IsKind(SyntaxKind.LogicalNotExpression) ||
            StripParens(negation.Operand) is not InvocationExpressionSyntax any ||
            !IsMember(any.Expression, "Any", out var cards) || !IsPileCards(cards, "Hand", ["Owner"]) ||
            any.ArgumentList.Arguments is not [var predicate] ||
            StripParens(predicate.Expression) is not ParenthesizedLambdaExpressionSyntax
            {
                ParameterList.Parameters: [ParameterSyntax { Type: IdentifierNameSyntax { Identifier.ValueText: "CardModel" } } card],
                ExpressionBody: { } body
            } ||
            StripParens(body) is not BinaryExpressionSyntax test || !test.IsKind(SyntaxKind.EqualsExpression))
            return false;
        return IsPath(test.Left, [card.Identifier.ValueText, "Type"]) && IsPath(test.Right, ["CardType", "Attack"]);
    }

    private static bool TryWalkInvocation(InvocationExpressionSyntax inv, WalkerContext ctx, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_command";

        if (IsVisualExpression(inv)) return true;

        if (inv.Expression is MemberAccessExpressionSyntax execMa && execMa.Name.Identifier.Text == "Execute")
        {
            if (TryWalkDamageCmdChain(inv, ctx, ops, out err, out cat))
                return true;
            if (cat != "not_damage_cmd")
                return false;
        }

        if (inv.Expression is MemberAccessExpressionSyntax ma)
        {
            string recv = ma.Expression.ToString();
            string mName = ma.Name.Identifier.Text;

            if (recv == "CreatureCmd" && mName == "GainBlock")
                return TryWalkGainBlock(inv, ctx, ops, out err, out cat);

            if (recv == "CreatureCmd" && mName == "Damage")
                return TryWalkCreatureDamage(inv, ctx, ops, out err, out cat);

            if (recv == "CreatureCmd" && mName == "Heal")
                return TryWalkHeal(inv, ctx, ops, out err, out cat);

            if (recv == "PowerCmd" && ma.Name is GenericNameSyntax gApply && gApply.Identifier.Text == "Apply")
                return TryWalkPowerApply(inv, gApply.TypeArgumentList.Arguments[0].ToString(), ctx, ops, out err, out cat);

            if (recv == "PowerCmd" && ma.Name is GenericNameSyntax gRem && gRem.Identifier.Text == "Remove")
                return TryWalkPowerRemove(inv, gRem.TypeArgumentList.Arguments[0].ToString(), ctx, ops, out err, out cat);

            if (recv == "CardPileCmd" && mName == "Draw")
                return TryWalkDraw(inv, ctx, ops, out err, out cat);

            if (recv == "PlayerCmd" && mName == "GainEnergy")
                return TryWalkGainResource(inv, ctx, ops, isStars: false, out err, out cat);
            if (recv == "PlayerCmd" && mName == "GainStars")
                return TryWalkGainResource(inv, ctx, ops, isStars: true, out err, out cat);

            if (ctx.IsCard && recv == "OrbCmd" && mName is "AddSlots" or "RemoveSlots")
            {
                var args = inv.ArgumentList.Arguments;
                if (!HasNamedArguments(args) && args is [var owner, var count] && IsPath(owner.Expression, ["Owner"]) &&
                    TryResolveInt(count.Expression, ctx, 0, out int value))
                {
                    ops.Add(mName == "AddSlots" ? new OpAddOrbSlots(value) : new OpRemoveOrbSlots(value));
                    return true;
                }
                err = $"Cannot resolve OrbCmd.{mName} arguments: {inv}";
                return false;
            }

            if (ctx.IsCard && IsPath(ma, ["EnergyCost", "AddThisCombat"]))
            {
                if (inv.ArgumentList.Arguments is [ArgumentSyntax { NameColon: null } amount] &&
                    TryResolveInt(amount.Expression, ctx, int.MinValue, out int value))
                {
                    ops.Add(new OpAddPlayedCardCombatCost(value));
                    return true;
                }
                err = $"Cannot resolve this card's combat cost modifier: {inv}";
                return false;
            }
            if (recv == "OrbCmd" && ma.Name is GenericNameSyntax gChan && gChan.Identifier.Text == "Channel")
                return TryWalkChannelOrb(gChan.TypeArgumentList.Arguments[0].ToString(), ops, out err, out cat);
            if (recv == "OrbCmd" && mName == "Channel")
                return TryWalkChannelOrbArg(inv, ops, out err, out cat);
            if (recv == "OrbCmd" && mName == "EvokeNext")
            {
                ops.Add(new OpEvokeOrb(1));
                return true;
            }

            if (recv == "ForgeCmd" && mName == "Forge")
            {
                var args = inv.ArgumentList.Arguments;
                if (args.Count >= 1 && TryResolveNumeric(args[0].Expression, ctx, out decimal amt))
                {
                    ops.Add(new OpForge(amt));
                    return true;
                }
                err = $"Cannot resolve ForgeCmd.Forge amount: {inv}";
                return false;
            }

            if (recv == "OstyCmd" && mName == "Summon")
            {
                var args = inv.ArgumentList.Arguments;
                if (args.Count >= 3 && TryResolveNumeric(args[2].Expression, ctx, out decimal amt))
                {
                    ops.Add(new OpSummonOsty(amt));
                    return true;
                }
                err = $"Cannot resolve OstyCmd.Summon amount: {inv}";
                return false;
            }

            if (recv == "CardPileCmd" && mName == "AddGeneratedCardToCombat")
                return TryWalkAddGeneratedCard(inv, ctx, ops, out err, out cat);

            if (recv == "CardCmd" && mName == "Discard")
                return TryWalkDiscard(inv, ctx, ops, out err, out cat);

            if (recv == "CardCmd" && mName == "Exhaust")
                return TryWalkExhaust(inv, ctx, ops, out err, out cat);

            if (mName == "Add" && ma.Expression is IdentifierNameSyntax listId && ctx.LocalCreatedCardList.TryGetValue(listId.Identifier.Text, out var lcInfo))
            {
                if (inv.ArgumentList.Arguments.Count == 1)
                {
                    var arg0 = inv.ArgumentList.Arguments[0].Expression;
                    string? addCls = null;
                    if (arg0 is IdentifierNameSyntax cid && ctx.LocalCreatedCardClass.TryGetValue(cid.Identifier.Text, out string? c1))
                        addCls = c1;
                    else if (TryMatchCreateCard(arg0, out string c2))
                        addCls = c2;
                    if (addCls != null && (string.IsNullOrEmpty(lcInfo.CardClass) || lcInfo.CardClass == addCls))
                    {
                        ctx.LocalCreatedCardList[listId.Identifier.Text] = (addCls, lcInfo.Count + 1);
                        return true;
                    }
                }
            }
        }

        err = $"Unsupported command call: {inv}";
        return false;
    }

    private static bool TryWalkDamageCmdChain(
        InvocationExpressionSyntax execInv, WalkerContext ctx, List<IrOp> ops, out string err, out string cat,
        string? hitCountLocal = null, PowerHitCount conditionalCount = default)
    {
        err = "";
        cat = "not_damage_cmd";
        var calls = new List<(string Method, ArgumentListSyntax Args)>();
        ExpressionSyntax? cur = execInv;
        while (cur is InvocationExpressionSyntax inv && inv.Expression is MemberAccessExpressionSyntax ma)
        {
            calls.Add((ma.Name.Identifier.Text, inv.ArgumentList));
            cur = ma.Expression;
        }
        calls.Reverse();
        if (calls.Count == 0 || cur == null || cur.ToString() != "DamageCmd" || calls[0].Method != "Attack")
            return false;

        cat = "unsupported_damage_cmd";
        var atkArgs = calls[0].Args.Arguments;
        if (atkArgs.Count < 1) { err = "DamageCmd.Attack missing amount"; return false; }

        IrTarget? target = ctx.IsMonster ? IrTarget.AllAllies : null;
        int hitCount = 1;
        bool usesConditionalCount = false;
        bool unpowered = false;
        bool unblockable = false;

        foreach (var (mName, args) in calls.Skip(1))
        {
            switch (mName)
            {
                case "FromCard":
                case "FromMonster":
                case "WithHitFx":
                case "WithHitVfxNode":
                case "WithHitVfxSpawnedAtBase":
                case "WithAttackerAnim":
                case "WithAttackerFx":
                case "WithWaitBeforeHit":
                case "WithNoAttackerAnim":
                case "OnlyPlayAnimOnce":
                case "SpawningHitVfxOnEachTarget":
                case "SpawningHitVfxOnEachCreature":
                case "Execute":
                    break;
                case "BeforeDamage":
                    if (args.Arguments.Count != 1 || !IsVisualAttackCallback(args.Arguments[0].Expression))
                    { err = $"Unsupported DamageCmd.BeforeDamage callback: {args}"; return false; }
                    break;
                case "Unpowered":
                    unpowered = true;
                    break;
                case "Unblockable":
                    unblockable = true;
                    break;
                case "WithHitCount":
                    if (args.Arguments.Count != 1) { err = "WithHitCount arity"; return false; }
                    if (hitCountLocal != null)
                    {
                        if (usesConditionalCount || !IsPath(args.Arguments[0].Expression, [hitCountLocal]))
                        { err = "Attack must use the conditional hit count exactly once"; return false; }
                        usesConditionalCount = true;
                        break;
                    }
                    if (ctx.IsMonster)
                    {
                        if (!TryResolveMonsterAscVal(args.Arguments[0].Expression, ctx, out var hAv) || !hAv.IsConst || hAv.BaseValue <= 0)
                        { err = $"Non-constant monster WithHitCount: {args.Arguments[0]}"; return false; }
                        hitCount = hAv.BaseValue;
                    }
                    else
                    {
                        if (!TryResolveNumeric(args.Arguments[0].Expression, ctx, out decimal hDec) || hDec <= 0 || hDec != decimal.Truncate(hDec))
                        { err = $"Non-constant WithHitCount: {args.Arguments[0]}"; return false; }
                        hitCount = (int)hDec;
                    }
                    break;
                case "Targeting":
                    if (args.Arguments.Count != 1 || !TryResolveTarget(args.Arguments[0].Expression, ctx, out IrTarget t1))
                    { err = $"Cannot resolve Targeting({args})"; return false; }
                    target = t1;
                    break;
                case "TargetingAllOpponents":
                    target = IrTarget.AllEnemies;
                    break;
                case "TargetingRandomOpponents":
                    target = IrTarget.RandomEnemy;
                    break;
                default:
                    err = $"Unsupported DamageCmd builder method: {mName}";
                    return false;
            }
        }

        if (target == null) { err = "DamageCmd chain missing target"; return false; }
        if (hitCountLocal != null && (!usesConditionalCount || target.Value != conditionalCount.Target))
        { err = "Conditional hit count must be used against the tested target"; return false; }

        if (ctx.IsMonster)
        {
            if (!TryResolveMonsterAscVal(atkArgs[0].Expression, ctx, out var dmgAsc))
            { err = $"Cannot resolve monster DamageCmd amount: {atkArgs[0]}"; return false; }
            ops.Add(new OpDealDamageAsc(target.Value, dmgAsc, hitCount, new IrProps(unpowered, unblockable, false, true)));
            return true;
        }
        else
        {
            var atkExpr = atkArgs[0].Expression;
            if (ctx.IsCard && StripParens(atkExpr) is MemberAccessExpressionSyntax &&
                TryResolveDynamicVarKey(atkExpr, ctx.ConstStrings, out var calculatedKey) &&
                ctx.Vars.TryGetValue(calculatedKey, out var calculated) && calculated.CalculatedSource != null)
            {
                if (calculated.Kind != "CalculatedDamage" || hitCountLocal != null || hitCount != 1 ||
                    target is not (IrTarget.ChosenTarget or IrTarget.Self) ||
                    calculated.DeclaredProps is not { } calculatedProps ||
                    !IsPath(calculatedProps, ["ValueProp", "Move"]) ||
                    !TryResolveCalculatedAmount(calculated, ctx, out var damage))
                { err = $"Unsupported calculated attack: {execInv}"; return false; }
                ops.Add(new OpDealDamageValue(target.Value, damage, hitCount, new IrProps(unpowered, unblockable, true, false)));
                return true;
            }
            if (TryResolveDamageOrBlockVar(atkExpr, ctx, out var dv))
            {
                unpowered |= dv.Unpowered;
                unblockable |= dv.Unblockable;
            }
            if (!TryResolveNumeric(atkExpr, ctx, out decimal dmgVal))
            { err = $"Cannot resolve DamageCmd amount: {atkExpr}"; return false; }
            var props = new IrProps(unpowered, unblockable, ctx.IsCard, false);
            ops.Add(usesConditionalCount
                ? new OpDealDamageIfPower(target.Value, conditionalCount, dmgVal, props)
                : new OpDealDamage(target.Value, dmgVal, hitCount, props));
            return true;
        }
    }

    private static bool TryWalkGainBlock(InvocationExpressionSyntax inv, WalkerContext ctx, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_gain_block";
        var args = inv.ArgumentList.Arguments;
        if (args.Count < 2) { err = $"GainBlock arity {args.Count}"; return false; }
        if (!TryResolveTarget(args[0].Expression, ctx, out IrTarget target))
        { err = $"Cannot resolve GainBlock target: {args[0]}"; return false; }

        if (ctx.IsMonster)
        {
            if (!TryResolveMonsterAscVal(args[1].Expression, ctx, out var blkAsc))
            { err = $"Cannot resolve monster GainBlock amount: {args[1]}"; return false; }
            bool unpow = args.Count >= 3 && ParseValuePropFlags(args[2].Expression).Unpowered;
            ops.Add(new OpGainBlockAsc(target, blkAsc, new IrProps(unpow, false, false, true)));
            return true;
        }

        if (ctx.IsCard && TryMatchBlockValue(args, ctx, out var value, out var runtimeProps))
        {
            ops.Add(new OpGainBlockValue(target, value, runtimeProps));
            return true;
        }
        if (TryResolveDamageOrBlockVar(args[1].Expression, ctx, out var bv) && bv.CalculatedSource == null)
        {
            var props = new IrProps(bv.Unpowered, false, ctx.IsCard, false);
            ops.Add(new OpGainBlock(target, bv.BaseValue, props));
            return true;
        }
        if (args.Count >= 3 && TryResolveNumeric(args[1].Expression, ctx, out decimal amt))
        {
            var (unpow, _) = ParseValuePropFlags(args[2].Expression);
            var props = new IrProps(unpow, false, ctx.IsCard, false);
            ops.Add(new OpGainBlock(target, amt, props));
            return true;
        }
        err = $"Cannot resolve GainBlock arguments: {inv}";
        return false;
    }

    private static bool TryMatchBlockValue(SeparatedSyntaxList<ArgumentSyntax> args, WalkerContext ctx,
        out RuntimeValue value, out IrProps props)
    {
        value = default;
        props = null!;
        if (args is not [var receiver, var amount, var propsArg, var play] || HasNamedArguments(args) ||
            !TryMatchPowerRecipient(receiver.Expression, out _) || !IsPath(play.Expression, ["cardPlay"]))
            return false;

        if (IsPath(amount.Expression, ["Owner", "Creature", "Block"]))
        {
            value = new RuntimeValue(ValueSource.ActorBlock, 0m, 1m);
        }
        else if (StripParens(amount.Expression) is InvocationExpressionSyntax calculate &&
            IsMember(calculate.Expression, "Calculate", out var variable) &&
            calculate.ArgumentList.Arguments is [ArgumentSyntax { NameColon: null } chosen] &&
            IsPath(chosen.Expression, ["cardPlay", "Target"]) &&
            TryResolveDynamicVarKey(variable, ctx.ConstStrings, out var valueKey) &&
            IsMember(propsArg.Expression, "Props", out var propsVariable) &&
            TryResolveDynamicVarKey(propsVariable, ctx.ConstStrings, out var propsKey) && valueKey == propsKey &&
            ctx.Vars.TryGetValue(valueKey, out var calculated) && calculated.Kind == "CalculatedBlock" &&
            TryResolveCalculatedAmount(calculated, ctx, out value))
        {
            // The calculation argument is the chosen target, not necessarily the
            // recipient of the resulting block.
        }
        else
        {
            return false;
        }
        if (!TryResolveDamageFlags(propsArg.Expression, ctx, out var flags) || flags.Unblockable)
            return false;
        props = new IrProps(flags.Unpowered, false, true, false, flags.Move);
        return true;
    }

    private static bool TryResolveCalculatedAmount(DynamicVarEntry calculated, WalkerContext ctx, out RuntimeValue value)
    {
        value = default;
        string extraKey = calculated.Kind == "CalculatedDamage" ? "ExtraDamage" : "CalculationExtra";
        if (calculated.CalculatedSource is not { } source ||
            !ctx.Vars.TryGetValue("CalculationBase", out var baseVar) || baseVar.Kind != "CalculationBaseVar" ||
            !ctx.Vars.TryGetValue(extraKey, out var multiplier) || multiplier.Kind != extraKey + "Var")
            return false;
        value = new RuntimeValue(source, baseVar.BaseValue, multiplier.BaseValue);
        return true;
    }

    private static bool TryWalkCreatureDamage(InvocationExpressionSyntax inv, WalkerContext ctx, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_creature_damage";
        var args = inv.ArgumentList.Arguments;
        if (args.Count < 4) { err = $"CreatureCmd.Damage arity {args.Count}"; return false; }
        if (!TryResolveTarget(args[1].Expression, ctx, out IrTarget target))
        { err = $"Cannot resolve CreatureCmd.Damage target: {args[1]}"; return false; }
        if (!TryResolveDamageFlags(args[3].Expression, ctx, out var flags))
        { err = $"Cannot resolve CreatureCmd.Damage properties: {args[3]}"; return false; }
        var props = new IrProps(flags.Unpowered, flags.Unblockable, ctx.IsCard, ctx.IsMonster, flags.Move);

        if (ctx.IsMonster)
        {
            if (!TryResolveMonsterAscVal(args[2].Expression, ctx, out var dmgAsc))
            { err = $"Cannot resolve monster CreatureCmd.Damage amount: {args[2]}"; return false; }
            ops.Add(new OpDealDamageAsc(target, dmgAsc, 1, props));
            return true;
        }

        if (TryResolveNumeric(args[2].Expression, ctx, out decimal amt))
        {
            ops.Add(new OpDealDamage(target, amt, 1, props));
            return true;
        }
        err = $"Cannot resolve CreatureCmd.Damage: {inv}";
        return false;
    }

    private static bool TryWalkHeal(InvocationExpressionSyntax inv, WalkerContext ctx, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_heal";
        var args = inv.ArgumentList.Arguments;
        if (args.Count < 2) { err = "Heal arity"; return false; }
        if (!TryResolveTarget(args[0].Expression, ctx, out IrTarget target))
        { err = $"Cannot resolve Heal target: {args[0]}"; return false; }
        if (!TryResolveNumeric(args[1].Expression, ctx, out decimal amt))
        { err = $"Cannot resolve Heal amount: {args[1]}"; return false; }
        ops.Add(new OpHeal(target, amt));
        return true;
    }

    private static bool TryWalkPowerApply(InvocationExpressionSyntax inv, string powerClass, WalkerContext ctx, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_power_apply";
        if (!ctx.Powers.TryGetValue(powerClass, out var pMeta))
        {
            err = $"Unknown Power class: {powerClass}";
            return false;
        }
        var args = inv.ArgumentList.Arguments;
        if (args.Count < 3) { err = $"PowerCmd.Apply arity {args.Count}"; return false; }
        ExpressionSyntax targetExpr = args[1].Expression;
        ExpressionSyntax amtExpr = args[2].Expression;
        if (!TryResolveTarget(targetExpr, ctx, out IrTarget target))
        { err = $"Cannot resolve PowerCmd.Apply target: {targetExpr}"; return false; }

        if (ctx.IsMonster)
        {
            if (!TryResolveMonsterAscVal(amtExpr, ctx, out var amtAsc))
            { err = $"Cannot resolve monster PowerCmd.Apply amount: {amtExpr}"; return false; }
            ops.Add(new OpApplyPowerAsc(target, pMeta, amtAsc));
            return true;
        }
        if (!TryResolveNumeric(amtExpr, ctx, out decimal amt))
        { err = $"Cannot resolve PowerCmd.Apply amount: {amtExpr}"; return false; }
        ops.Add(new OpApplyPower(target, pMeta, amt));
        return true;
    }

    private static bool TryWalkPowerRemove(InvocationExpressionSyntax inv, string powerClass, WalkerContext ctx, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_power_remove";
        if (!ctx.Powers.TryGetValue(powerClass, out var pMeta))
        { err = $"Unknown Power class: {powerClass}"; return false; }
        var args = inv.ArgumentList.Arguments;
        if (args.Count != 1 || !TryResolveTarget(args[0].Expression, ctx, out IrTarget target))
        { err = $"Cannot resolve PowerCmd.Remove target: {inv}"; return false; }
        ops.Add(new OpRemovePower(target, pMeta.EntryId));
        return true;
    }

    private static bool TryWalkDraw(InvocationExpressionSyntax inv, WalkerContext ctx, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_draw";
        var args = inv.ArgumentList.Arguments;
        if (args.Count == 2)
        {
            ops.Add(new OpDraw(1));
            return true;
        }
        if (args.Count >= 3 && TryResolveNumeric(args[1].Expression, ctx, out decimal count) && count == decimal.Truncate(count) && count >= 0)
        {
            ops.Add(new OpDraw((int)count));
            return true;
        }
        err = $"Cannot resolve CardPileCmd.Draw: {inv}";
        return false;
    }

    private static bool TryWalkGainResource(InvocationExpressionSyntax inv, WalkerContext ctx, List<IrOp> ops, bool isStars, out string err, out string cat)
    {
        err = "";
        cat = isStars ? "unsupported_gain_stars" : "unsupported_gain_energy";
        var args = inv.ArgumentList.Arguments;
        if (!isStars && ctx.IsCard && args is [var current, var owner] && !HasNamedArguments(args) &&
            IsPath(current.Expression, ["Owner", "PlayerCombatState", "Energy"]) && IsPath(owner.Expression, ["Owner"]))
        {
            ops.Add(new OpGainCurrentEnergy());
            return true;
        }
        if (args.Count >= 1 && TryResolveNumeric(args[0].Expression, ctx, out decimal amt) && amt == decimal.Truncate(amt) && amt >= 0)
        {
            ops.Add(isStars ? new OpGainStars((int)amt) : new OpGainEnergy((int)amt));
            return true;
        }
        err = $"Cannot resolve resource amount: {inv}";
        return false;
    }

    private static bool TryWalkChannelOrb(string orbCls, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_orb_channel";
        if (TryMapOrbKind(orbCls, out var kind))
        {
            ops.Add(new OpChannelOrb(kind));
            return true;
        }
        err = $"Unknown Orb class: {orbCls}";
        return false;
    }

    private static bool TryWalkChannelOrbArg(InvocationExpressionSyntax inv, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_orb_channel";
        var args = inv.ArgumentList.Arguments;
        if (args.Count >= 2 && args[1].Expression is ObjectCreationExpressionSyntax obj && TryMapOrbKind(obj.Type.ToString(), out var kind))
        {
            ops.Add(new OpChannelOrb(kind));
            return true;
        }
        err = $"Unsupported OrbCmd.Channel arg: {inv}";
        return false;
    }

    private static bool TryWalkAddGeneratedCard(InvocationExpressionSyntax inv, WalkerContext ctx, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_add_generated_card";
        var args = inv.ArgumentList.Arguments;
        if (args.Count < 2) { err = "AddGeneratedCardToCombat arity"; return false; }

        string? cardCls = null;
        int count = 1;
        var a0 = args[0].Expression;
        if (a0 is IdentifierNameSyntax id0 && ctx.LocalCreatedCardClass.TryGetValue(id0.Identifier.Text, out string? c1))
            cardCls = c1;
        else if (a0 is IdentifierNameSyntax idList && ctx.LocalCreatedCardList.TryGetValue(idList.Identifier.Text, out var listInfo) && !string.IsNullOrEmpty(listInfo.CardClass))
        {
            cardCls = listInfo.CardClass;
            count = listInfo.Count;
        }
        else if (TryMatchCreateCard(a0, out string c2))
            cardCls = c2;

        if (cardCls == null || !ctx.CardMetas.TryGetValue(cardCls, out var cMeta))
        { err = $"Cannot resolve generated card class: {a0}"; return false; }

        if (!TryParsePileType(args[1].Expression.ToString(), out string pile))
        { err = $"Cannot resolve PileType: {args[1]}"; return false; }

        string pos = "bottom";
        if (args.Count >= 4)
        {
            string ps = args[3].Expression.ToString();
            if (ps.Contains("Top", StringComparison.Ordinal)) pos = "top";
            else if (ps.Contains("Random", StringComparison.Ordinal)) pos = "random";
        }
        ops.Add(new OpAddGeneratedCard(cMeta.EntryId, cMeta.CardType, cMeta.BaseCost, pile, count, pos));
        return true;
    }

    private static bool TryWalkDiscard(InvocationExpressionSyntax inv, WalkerContext ctx, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_discard";
        var args = inv.ArgumentList.Arguments;
        if (args.Count < 2) { err = "Discard arity"; return false; }
        string a1 = args[1].Expression.ToString();
        if (a1.Contains("PileType.Hand", StringComparison.Ordinal))
        {
            ops.Add(new OpDiscardAllHand());
            return true;
        }
        if (args[1].Expression is IdentifierNameSyntax id && ctx.LocalSelectedCards.TryGetValue(id.Identifier.Text, out var sel))
        {
            ops.Add(new OpDiscardChosen(ctx.NextChoiceId++, sel.Count));
            return true;
        }
        err = $"Unsupported CardCmd.Discard target: {a1}";
        return false;
    }

    private static bool TryWalkExhaust(InvocationExpressionSyntax inv, WalkerContext ctx, List<IrOp> ops, out string err, out string cat)
    {
        err = "";
        cat = "unsupported_exhaust";
        var args = inv.ArgumentList.Arguments;
        if (args.Count < 2) { err = "Exhaust arity"; return false; }
        string a1 = args[1].Expression.ToString();
        if (a1 == "this")
        {
            ops.Add(new OpExhaustSelf());
            return true;
        }
        if (args[1].Expression is IdentifierNameSyntax id && ctx.LocalSelectedCards.TryGetValue(id.Identifier.Text, out var sel))
        {
            ops.Add(new OpExhaustChosen(ctx.NextChoiceId++, sel.Count));
            return true;
        }
        err = $"Unsupported CardCmd.Exhaust target: {a1}";
        return false;
    }

    // =========================================================================
    // Expression Resolution Helpers
    // =========================================================================
    private static bool TryResolveTarget(ExpressionSyntax expr, WalkerContext ctx, out IrTarget target)
    {
        expr = UnwrapExpr(expr);
        string s = expr.ToString();
        if (expr is IdentifierNameSyntax id && ctx.LocalTargets.TryGetValue(id.Identifier.Text, out var lt))
        {
            target = lt;
            return true;
        }
        if (s is "Owner.Creature" or "Creature" or "base.Creature" or "this.Creature" or "base.Owner.Creature")
        {
            target = IrTarget.Self;
            return true;
        }
        if (s is "cardPlay.Target" or "cardPlay.Target!" or "play.Target")
        {
            target = IrTarget.ChosenTarget;
            return true;
        }
        if (s == "target" && ctx.IsPotion)
        {
            target = ctx.PotionTargetSelfByDefault ? IrTarget.Self : IrTarget.ChosenTarget;
            return true;
        }
        if (s == "targets" && ctx.IsMonster)
        {
            target = IrTarget.AllAllies;
            return true;
        }
        if (s.EndsWith("HittableEnemies", StringComparison.Ordinal) ||
            s.EndsWith("Enemies", StringComparison.Ordinal))
        {
            target = IrTarget.AllEnemies;
            return true;
        }
        if (s.EndsWith("PlayerCreatures", StringComparison.Ordinal) ||
            s.EndsWith("Allies", StringComparison.Ordinal))
        {
            target = IrTarget.AllAllies;
            return true;
        }
        target = IrTarget.Self;
        return false;
    }

    private static bool TryResolveDamageOrBlockVar(ExpressionSyntax expr, WalkerContext ctx, out DynamicVarEntry entry)
    {
        expr = UnwrapExpr(expr);
        if (expr is IdentifierNameSyntax id && ctx.LocalVarAliases.TryGetValue(id.Identifier.Text, out var alias))
        {
            entry = alias;
            return true;
        }
        if (expr is MemberAccessExpressionSyntax ma &&
            ma.Name.Identifier.Text is "BaseValue" or "IntValue" &&
            TryResolveDamageOrBlockVar(ma.Expression, ctx, out entry))
            return true;

        if (TryResolveDynamicVarKey(expr, ctx.ConstStrings, out string key) && ctx.Vars.TryGetValue(key, out var dv))
        {
            entry = dv;
            return true;
        }
        entry = null!;
        return false;
    }

    private static bool TryResolveNumeric(ExpressionSyntax expr, WalkerContext ctx, out decimal val)
    {
        expr = UnwrapExpr(expr);
        if (TryEvalDecimalExpr(expr, ctx.ConstNumbers, out val))
            return true;
        if (expr is IdentifierNameSyntax id)
        {
            if (ctx.LocalNums.TryGetValue(id.Identifier.Text, out val)) return true;
            if (ctx.LocalVarAliases.TryGetValue(id.Identifier.Text, out var dvAlias) && dvAlias.CalculatedSource == null)
            {
                val = dvAlias.BaseValue;
                return true;
            }
        }
        if (expr is MemberAccessExpressionSyntax ma &&
            ma.Name.Identifier.Text is "BaseValue" or "IntValue")
        {
            if (ma.Expression is IdentifierNameSyntax aid && ctx.LocalVarAliases.TryGetValue(aid.Identifier.Text, out var adv) &&
                adv.CalculatedSource == null)
            {
                val = adv.BaseValue;
                return true;
            }
            if (TryResolveDynamicVarKey(ma.Expression, ctx.ConstStrings, out string key) && ctx.Vars.TryGetValue(key, out var dv) &&
                dv.CalculatedSource == null)
            {
                val = dv.BaseValue;
                return true;
            }
        }
        if (TryResolveDynamicVarKey(expr, ctx.ConstStrings, out string dKey) && ctx.Vars.TryGetValue(dKey, out var dvDirect) &&
            dvDirect.CalculatedSource == null)
        {
            val = dvDirect.BaseValue;
            return true;
        }
        if (expr is BinaryExpressionSyntax bin &&
            TryResolveNumeric(bin.Left, ctx, out decimal l) &&
            TryResolveNumeric(bin.Right, ctx, out decimal r))
        {
            if (bin.IsKind(SyntaxKind.AddExpression)) { val = l + r; return true; }
            if (bin.IsKind(SyntaxKind.SubtractExpression)) { val = l - r; return true; }
            if (bin.IsKind(SyntaxKind.MultiplyExpression)) { val = l * r; return true; }
        }
        if (expr is PrefixUnaryExpressionSyntax pre && pre.IsKind(SyntaxKind.UnaryMinusExpression) &&
            TryResolveNumeric(pre.Operand, ctx, out decimal inner))
        {
            val = -inner;
            return true;
        }
        val = 0m;
        return false;
    }

    private static bool TryResolveMonsterAscVal(ExpressionSyntax expr, WalkerContext ctx, out AscVal val)
    {
        expr = UnwrapExpr(expr);
        if (TryEvalIntLiteral(expr, out int lit))
        {
            val = AscVal.Const(lit);
            return true;
        }
        if (expr is IdentifierNameSyntax id)
        {
            if (ctx.LocalAscs.TryGetValue(id.Identifier.Text, out val!)) return true;
            if (ctx.MonsterAscProps.TryGetValue(id.Identifier.Text, out val!)) return true;
        }
        if (expr is MemberAccessExpressionSyntax ma && ma.Expression is ThisExpressionSyntax &&
            ctx.MonsterAscProps.TryGetValue(ma.Name.Identifier.Text, out val!))
            return true;
        if (TryEvalAscVal(expr, ctx.MonsterAscProps, out val))
            return true;
        if (expr is PrefixUnaryExpressionSyntax pre && pre.IsKind(SyntaxKind.UnaryMinusExpression) &&
            TryResolveMonsterAscVal(pre.Operand, ctx, out var inner))
        {
            val = new AscVal(inner.Threshold, -inner.AscValue, -inner.BaseValue);
            return true;
        }
        val = AscVal.Const(0);
        return false;
    }

    private static bool TryResolveDynamicVarKey(ExpressionSyntax expr, Dictionary<string, string> constStrings, out string key)
    {
        expr = UnwrapExpr(expr);
        key = "";
        if (expr is MemberAccessExpressionSyntax ma)
        {
            string recv = ma.Expression.ToString();
            if (recv is "DynamicVars" or "base.DynamicVars" or "this.DynamicVars")
            {
                // These properties in DynamicVarSet index the canonical power key.
                key = ma.Name.Identifier.ValueText switch
                {
                    "Dexterity" => "DexterityPower",
                    "Doom" => "DoomPower",
                    "Poison" => "PoisonPower",
                    "Strength" => "StrengthPower",
                    "Vulnerable" => "VulnerablePower",
                    "Weak" => "WeakPower",
                    var name => name
                };
                return true;
            }
        }
        if (expr is ElementAccessExpressionSyntax ea)
        {
            string recv = ea.Expression.ToString();
            if ((recv is "DynamicVars" or "base.DynamicVars" or "this.DynamicVars") &&
                ea.ArgumentList.Arguments.Count == 1 &&
                TryEvalString(ea.ArgumentList.Arguments[0].Expression, constStrings, out key))
                return true;
        }
        return false;
    }

    private static bool TryMatchCreateCard(ExpressionSyntax expr, out string cardClass)
    {
        cardClass = "";
        expr = UnwrapExpr(expr);
        if (expr is InvocationExpressionSyntax inv &&
            inv.Expression is MemberAccessExpressionSyntax ma &&
            ma.Name is GenericNameSyntax g &&
            g.Identifier.Text == "CreateCard" &&
            g.TypeArgumentList.Arguments.Count == 1)
        {
            cardClass = g.TypeArgumentList.Arguments[0].ToString();
            return true;
        }
        return false;
    }

    private static bool TryMatchCardSelect(ExpressionSyntax expr, WalkerContext ctx, out string kind, out int count)
    {
        kind = "";
        count = 1;
        expr = UnwrapExpr(expr);
        if (expr is InvocationExpressionSyntax outerInv && outerInv.Expression is MemberAccessExpressionSyntax outerMa &&
            outerMa.Name.Identifier.Text is "FirstOrDefault" or "ToList")
        {
            expr = UnwrapAwait(UnwrapExpr(outerMa.Expression));
        }
        if (expr is InvocationExpressionSyntax inv && inv.Expression is MemberAccessExpressionSyntax ma &&
            ma.Expression.ToString() == "CardSelectCmd" &&
            ma.Name.Identifier.Text is "FromHandForDiscard" or "FromHand")
        {
            var prefsObj = inv.DescendantNodes().OfType<ObjectCreationExpressionSyntax>()
                .FirstOrDefault(o => o.Type.ToString().EndsWith("CardSelectorPrefs", StringComparison.Ordinal));
            if (prefsObj != null && prefsObj.ArgumentList != null && prefsObj.ArgumentList.Arguments.Count >= 2 &&
                TryResolveNumeric(prefsObj.ArgumentList.Arguments[1].Expression, ctx, out decimal cDec) &&
                cDec >= 1 && cDec == decimal.Truncate(cDec))
            {
                bool hasFilter = inv.ArgumentList.Arguments.Any(a =>
                    (a.NameColon?.Name.Identifier.Text == "filter" && !a.Expression.IsKind(SyntaxKind.NullLiteralExpression)) ||
                    a.Expression is LambdaExpressionSyntax);
                if (hasFilter) return false;
                kind = ma.Name.Identifier.Text;
                count = (int)cDec;
                return true;
            }
        }
        return false;
    }

    private static bool TryMapOrbKind(string cls, out IrOrbKind kind)
    {
        int dot = cls.LastIndexOf('.');
        string name = dot >= 0 ? cls[(dot + 1)..] : cls;
        switch (name)
        {
            case "LightningOrb": kind = IrOrbKind.Lightning; return true;
            case "FrostOrb": kind = IrOrbKind.Frost; return true;
            case "DarkOrb": kind = IrOrbKind.Dark; return true;
            case "PlasmaOrb": kind = IrOrbKind.Plasma; return true;
            case "GlassOrb": kind = IrOrbKind.Glass; return true;
            default: kind = IrOrbKind.Lightning; return false;
        }
    }

    private static bool TryParsePileType(string exprText, out string pile)
    {
        if (exprText.EndsWith("PileType.Hand", StringComparison.Ordinal)) { pile = "hand"; return true; }
        if (exprText.EndsWith("PileType.Draw", StringComparison.Ordinal)) { pile = "draw"; return true; }
        if (exprText.EndsWith("PileType.Discard", StringComparison.Ordinal)) { pile = "discard"; return true; }
        if (exprText.EndsWith("PileType.Exhaust", StringComparison.Ordinal)) { pile = "exhaust"; return true; }
        pile = "";
        return false;
    }

    private static (bool Unpowered, bool Unblockable) ParseValuePropFlags(ExpressionSyntax expr)
    {
        string s = expr.ToString();
        bool unpow = s.Contains("ValueProp.Unpowered", StringComparison.Ordinal);
        bool unblk = s.Contains("ValueProp.Unblockable", StringComparison.Ordinal);
        return (unpow, unblk);
    }

    private static bool TryResolveDamageFlags(ExpressionSyntax expr, WalkerContext ctx,
        out (bool Unpowered, bool Unblockable, bool Move) flags)
    {
        expr = UnwrapExpr(expr);
        if (expr is MemberAccessExpressionSyntax access && access.Name.Identifier.Text == "Props" &&
            TryResolveDamageOrBlockVar(access.Expression, ctx, out var dv) && dv.DeclaredProps is { } declared)
            return TryParseDamageFlags(declared, out flags);
        return TryParseDamageFlags(expr, out flags);
    }

    private static bool TryParseDamageFlags(ExpressionSyntax expr,
        out (bool Unpowered, bool Unblockable, bool Move) flags)
    {
        expr = UnwrapExpr(expr);
        flags = default;
        if (expr is MemberAccessExpressionSyntax { Expression: IdentifierNameSyntax id } access &&
            id.Identifier.Text == "ValueProp")
        {
            string member = access.Name.Identifier.Text;
            flags = (member == "Unpowered", member == "Unblockable", member == "Move");
            return member is "Unpowered" or "Unblockable" or "Move" or "SkipHurtAnim";
        }
        if (expr is BinaryExpressionSyntax binary && binary.IsKind(SyntaxKind.BitwiseOrExpression) &&
            TryParseDamageFlags(binary.Left, out var left) && TryParseDamageFlags(binary.Right, out var right))
        {
            flags = (left.Unpowered || right.Unpowered, left.Unblockable || right.Unblockable, left.Move || right.Move);
            return true;
        }
        return false;
    }

    private static bool IsIgnorableVisualStatement(StatementSyntax stmt)
    {
        if (stmt is ExpressionStatementSyntax es)
            return IsVisualExpression(UnwrapAwait(es.Expression));
        if (stmt is LocalDeclarationStatementSyntax ld)
            return ld.Declaration.Variables.All(v => v.Initializer != null && IsVisualExpression(UnwrapAwait(v.Initializer.Value)));
        return false;
    }

    private static bool IsVisualBlockOrStmt(StatementSyntax stmt)
    {
        if (stmt is BlockSyntax b)
            return b.Statements.All(IsVisualBlockOrStmt);
        return IsIgnorableVisualStatement(stmt);
    }

    private static bool IsVisualExpression(ExpressionSyntax expr)
    {
        return UnwrapExpr(expr) switch
        {
            ConditionalAccessExpressionSyntax c when c.Expression.ToString() == "NCombatRoom.Instance" =>
                c.WhenNotNull is InvocationExpressionSyntax call &&
                call.Expression.ToString() is ".GetCreatureNode" or ".GetCreatureNodeIncludingDying"
                    or ".CombatVfxContainer.AddChildSafely" or ".PlaySplashVfx" or ".RadialBlur",
            InvocationExpressionSyntax { Expression: MemberAccessExpressionSyntax ma } =>
                (ma.Expression.ToString(), ma.Name.Identifier.Text) switch
                {
                    ("VfxCmd" or "SfxCmd" or "TalkCmd" or "NPowerUpVfx" or "NDebugAudioManager", _) => true,
                    ("NCombatRoom.Instance", "GetCreatureNode" or "GetCreatureNodeIncludingDying" or "PlaySplashVfx" or "RadialBlur") => true,
                    ("NCombatRoom.Instance.CombatVfxContainer", "AddChildSafely") => true,
                    ("MelodyCmd", "PlayMelodyVfx") => true,
                    ("Cmd", "Wait" or "CustomScaledWait") => true,
                    ("CreatureCmd", "TriggerAnim") => true,
                    ("ArgumentNullException", "ThrowIfNull") => true,
                    ("PotionModel", var name) when name.StartsWith("AssertValid", StringComparison.Ordinal) => true,
                    ("CardCmd", "PreviewCardPileAdd") => true,
                    (_, "Create") when ma.Expression is IdentifierNameSyntax receiver =>
                        receiver.Identifier.Text.EndsWith("Vfx", StringComparison.Ordinal),
                    _ => false
                },
            _ => false
        };
    }

    private static bool IsVisualAttackCallback(ExpressionSyntax callback)
    {
        if (callback is LambdaExpressionSyntax lambda)
            return lambda.Body switch
            {
                BlockSyntax block => IsVisualBlockOrStmt(block),
                ExpressionSyntax expression => IsVisualExpression(UnwrapAwait(expression)),
                _ => false
            };
        // This audio callback advances only its SFX parameter, not combat state.
        if (callback is not IdentifierNameSyntax { Identifier.Text: "PlayAttackSfx" } ||
            callback.FirstAncestorOrSelf<ClassDeclarationSyntax>() is not { } cls)
            return false;
        var method = cls.Members.OfType<MethodDeclarationSyntax>()
            .SingleOrDefault(m => m.Identifier.Text == "PlayAttackSfx" && m.ParameterList.Parameters.Count == 0);
        return method?.Body is { } body && body.Statements.All(s =>
            IsIgnorableVisualStatement(s) ||
            s is ReturnStatementSyntax { Expression: { } result } && result.ToString() == "Task.CompletedTask" ||
            s is ExpressionStatementSyntax { Expression: AssignmentExpressionSyntax a } &&
            a.IsKind(SyntaxKind.AddAssignmentExpression) && a.Left.ToString() == "AttackSfxStrength" &&
            a.Right is LiteralExpressionSyntax);
    }

    private static string ExtractMethodName(ExpressionSyntax expr)
    {
        expr = UnwrapExpr(expr);
        if (expr is IdentifierNameSyntax id) return id.Identifier.Text;
        if (expr is MemberAccessExpressionSyntax ma) return ma.Name.Identifier.Text;
        return "";
    }

    private static ExpressionSyntax UnwrapAwait(ExpressionSyntax e)
    {
        e = UnwrapExpr(e);
        if (e is AwaitExpressionSyntax aw) return UnwrapExpr(aw.Expression);
        return e;
    }

    private static ExpressionSyntax StripParens(ExpressionSyntax expression)
    {
        while (expression is ParenthesizedExpressionSyntax paren)
            expression = paren.Expression;
        return expression;
    }

    private static bool IsMember(ExpressionSyntax expression, string member, out ExpressionSyntax receiver)
    {
        if (StripParens(expression) is MemberAccessExpressionSyntax
            {
                Name: IdentifierNameSyntax name
            } access && name.Identifier.ValueText == member)
        {
            receiver = access.Expression;
            return true;
        }
        receiver = null!;
        return false;
    }

    private static bool IsPath(ExpressionSyntax expression, ReadOnlySpan<string> path)
    {
        for (int i = path.Length - 1; i > 0; i--)
        {
            if (!IsMember(expression, path[i], out expression))
                return false;
        }
        return StripParens(expression) switch
        {
            IdentifierNameSyntax root => root.Identifier.ValueText == path[0],
            ThisExpressionSyntax => path[0] == "this",
            _ => false
        };
    }

    private static bool IsPileCards(ExpressionSyntax expression, string pile, ReadOnlySpan<string> owner) =>
        IsMember(expression, "Cards", out var receiver) &&
        StripParens(receiver) is InvocationExpressionSyntax getPile &&
        IsMember(getPile.Expression, "GetPile", out var pileType) && IsPath(pileType, ["PileType", pile]) &&
        getPile.ArgumentList.Arguments is [ArgumentSyntax { NameColon: null } player] && IsPath(player.Expression, owner);

    private static bool HasNamedArguments(SeparatedSyntaxList<ArgumentSyntax> args)
    {
        foreach (var arg in args)
            if (arg.NameColon != null) return true;
        return false;
    }

    private static bool TryResolveInt(ExpressionSyntax expression, WalkerContext ctx, int minimum, out int value)
    {
        value = 0;
        if (!TryResolveNumeric(expression, ctx, out decimal number) || number < minimum ||
            number > int.MaxValue || number != decimal.Truncate(number))
            return false;
        value = (int)number;
        return true;
    }

    private static ExpressionSyntax UnwrapExpr(ExpressionSyntax e)
    {
        while (true)
        {
            if (e is ParenthesizedExpressionSyntax p) { e = p.Expression; continue; }
            if (e is PostfixUnaryExpressionSyntax pu && pu.IsKind(SyntaxKind.SuppressNullableWarningExpression)) { e = pu.Operand; continue; }
            if (e is CastExpressionSyntax ce && ce.Type.ToString() is "decimal" or "int" or "float") { e = ce.Expression; continue; }
            return e;
        }
    }

    private static ExpressionSyntax UnwrapCastAndParen(ExpressionSyntax e)
    {
        while (true)
        {
            if (e is ParenthesizedExpressionSyntax p) { e = p.Expression; continue; }
            if (e is CastExpressionSyntax c) { e = c.Expression; continue; }
            return e;
        }
    }

    private static bool TryEvalString(ExpressionSyntax expr, Dictionary<string, string> constStrings, out string result)
    {
        expr = UnwrapExpr(expr);
        if (expr is LiteralExpressionSyntax lit && lit.IsKind(SyntaxKind.StringLiteralExpression))
        {
            result = lit.Token.ValueText;
            return true;
        }
        if (expr is IdentifierNameSyntax id && constStrings.TryGetValue(id.Identifier.Text, out result!))
            return true;
        result = "";
        return false;
    }

    private static bool TryEvalIntLiteral(ExpressionSyntax expr, out int val)
    {
        expr = UnwrapExpr(expr);
        if (TryEvalDecimalLiteral(expr, out decimal d) && d == decimal.Truncate(d) && d >= int.MinValue && d <= int.MaxValue)
        {
            val = (int)d;
            return true;
        }
        val = 0;
        return false;
    }

    private static bool TryEvalDecimalLiteral(ExpressionSyntax expr, out decimal val)
    {
        expr = UnwrapExpr(expr);
        if (expr is LiteralExpressionSyntax lit && lit.IsKind(SyntaxKind.NumericLiteralExpression))
        {
            object? raw = lit.Token.Value;
            if (raw is int i) { val = i; return true; }
            if (raw is long l) { val = l; return true; }
            if (raw is decimal m) { val = m; return true; }
            if (raw is float f) { val = (decimal)f; return true; }
            if (raw is double db) { val = (decimal)db; return true; }
        }
        if (expr is PrefixUnaryExpressionSyntax pre && pre.IsKind(SyntaxKind.UnaryMinusExpression) &&
            TryEvalDecimalLiteral(pre.Operand, out decimal inner))
        {
            val = -inner;
            return true;
        }
        val = 0m;
        return false;
    }

    private static bool TryEvalDecimalExpr(ExpressionSyntax expr, Dictionary<string, decimal> constNums, out decimal val)
    {
        expr = UnwrapExpr(expr);
        if (TryEvalDecimalLiteral(expr, out val)) return true;
        if (expr is IdentifierNameSyntax id && constNums.TryGetValue(id.Identifier.Text, out val)) return true;
        val = 0m;
        return false;
    }

    // =========================================================================
    // Lean 4 & C# Code Generators
    // =========================================================================
    private static string LeanStr(string s) => "\"" + s.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\"";

    private static string LeanDec(decimal d)
    {
        if (d == decimal.Truncate(d))
        {
            long n = (long)d;
            return n < 0 ? $"(Dec.ofInt ({n}))" : $"(Dec.ofInt {n})";
        }
        string s = d.ToString(CultureInfo.InvariantCulture);
        int dot = s.IndexOf('.');
        int scale = s.Length - dot - 1;
        string digits = s.Replace(".", "");
        long scaled = long.Parse(digits, CultureInfo.InvariantCulture);
        return scaled < 0 ? $"(Dec.ofScaled ({scaled}) {scale})" : $"(Dec.ofScaled {scaled} {scale})";
    }

    private static string LeanTarget(IrTarget t) => t switch
    {
        IrTarget.Self => ".self",
        IrTarget.ChosenTarget => ".chosenTarget",
        IrTarget.AllEnemies => ".allEnemies",
        IrTarget.RandomEnemy => ".randomEnemy",
        IrTarget.AllAllies => ".allAllies",
        IrTarget.FirstLivingPlayer => ".firstLivingPlayer",
        _ => ".self"
    };

    private static string LeanOrb(IrOrbKind k) => k switch
    {
        IrOrbKind.Lightning => ".lightning",
        IrOrbKind.Frost => ".frost",
        IrOrbKind.Dark => ".dark",
        IrOrbKind.Plasma => ".plasma",
        IrOrbKind.Glass => ".glass",
        _ => ".lightning"
    };

    private static string LeanDmgProps(IrProps p)
    {
        if (p.Move && !p.Unpowered && !p.Unblockable)
            return p.IsMonster ? "DamageProps.monsterMove" : "DamageProps.card";
        if (p.Unpowered && !p.Move)
            return p.Unblockable ? "DamageProps.nonCardHpLoss" : "DamageProps.nonCardUnpowered";
        if (p.Unpowered && p.Move)
            return p.Unblockable ? "DamageProps.cardHpLoss" : "DamageProps.cardUnpowered";
        return $"{{ move := {(p.Move ? "true" : "false")}, unblockable := {(p.Unblockable ? "true" : "false")} }}";
    }

    private static string LeanBlkProps(IrProps p)
    {
        if (p.Unpowered) return "BlockProps.nonCardUnpowered";
        return p.IsMonster ? "BlockProps.monsterMove" : "BlockProps.card";
    }

    private static string LeanRuntimeBlockProps(IrProps p)
    {
        if (p.Move) return p.Unpowered ? "BlockProps.cardUnpowered" : "BlockProps.card";
        return p.Unpowered ? "BlockProps.nonCardUnpowered" : "{}";
    }

    private static string RuntimeValueName(ValueSource source) => source switch
    {
        ValueSource.ActorBlock => "actorBlock",
        ValueSource.ChosenBlock => "chosenBlock",
        ValueSource.DiscardCount => "discardCount",
        _ => throw new ArgumentOutOfRangeException(nameof(source))
    };

    private static string LeanRuntimeValue(RuntimeValue value) =>
        $"(.{RuntimeValueName(value.Source)} {LeanDec(value.Base)} {LeanDec(value.Multiplier)})";

    private static string LeanInt(int value) =>
        value < 0 ? $"({value.ToString(CultureInfo.InvariantCulture)})" : value.ToString(CultureInfo.InvariantCulture);

    private static string LeanPowerTemplate(PowerMeta p) =>
        $"mkGenPower {LeanStr(p.EntryId)} .{p.PowerType} .{p.StackType} .{p.InstanceType} {(p.AllowNegative ? "true" : "false")}";

    private static string LeanAscVal(AscVal av)
    {
        string a = av.AscValue < 0 ? $"({av.AscValue})" : av.AscValue.ToString(CultureInfo.InvariantCulture);
        string b = av.BaseValue < 0 ? $"({av.BaseValue})" : av.BaseValue.ToString(CultureInfo.InvariantCulture);
        return av.IsConst
            ? $"(AscensionVal.const {b})"
            : $"{{ threshold := {av.Threshold}, ascVal := {a}, baseVal := {b} }}";
    }

    private static string LeanOp(IrOp op) => op switch
    {
        OpDealDamage d => $".dealDamage {LeanTarget(d.Target)} {LeanDec(d.Amount)} {d.Hits} {LeanDmgProps(d.Props)}",
        OpGainBlock b => $".gainBlock {LeanTarget(b.Target)} {LeanDec(b.Amount)} {LeanBlkProps(b.Props)}",
        OpApplyPower p => $".applyPower {LeanTarget(p.Target)} ({LeanPowerTemplate(p.Power)}) {LeanDec(p.Amount)}",
        OpRemovePower r => $".removePower {LeanTarget(r.Target)} (ModelId.mkPower {LeanStr(r.PowerEntryId)})",
        OpDraw dr => $".draw {dr.Count}",
        OpDiscardChosen dc => $".discardChosen {dc.ChoiceId} {dc.Count}",
        OpDiscardAllHand => ".discardAllHand",
        OpExhaustSelf => ".exhaustSelf",
        OpExhaustChosen ec => $".exhaustChosen {ec.ChoiceId} {ec.Count}",
        OpGainEnergy ge => $".gainEnergy {ge.Amount}",
        OpGainStars gs => $".gainStars {gs.Amount}",
        OpHeal h => $".heal {LeanTarget(h.Target)} {LeanDec(h.Amount)}",
        OpChannelOrb o => $".channelOrb {LeanOrb(o.Kind)}",
        OpEvokeOrb e => $".evokeOrb {e.Times}",
        OpForge f => $".forge {LeanDec(f.Amount)}",
        OpAddGeneratedCard g => $".addGeneratedCard {LeanStr(g.CardEntry)} .{g.CardType} {(g.Cost < 0 ? $"({g.Cost})" : g.Cost.ToString(CultureInfo.InvariantCulture))} .{g.Pile} {g.Count} .{g.Pos}",
        OpSummonOsty s => $".summonOsty {LeanDec(s.Amount)}",
        OpDealDamageAsc d => $".dealDamageAsc {LeanTarget(d.Target)} {LeanAscVal(d.Amt)} {d.Hits} {LeanDmgProps(d.Props)}",
        OpGainBlockAsc b => $".gainBlockAsc {LeanTarget(b.Target)} {LeanAscVal(b.Amt)} {LeanBlkProps(b.Props)}",
        OpApplyPowerAsc p => $".applyPowerAsc {LeanTarget(p.Target)} ({LeanPowerTemplate(p.Power)}) {LeanAscVal(p.Amt)}",
        OpAddOrbSlots add => $".addOrbSlots {add.Count}",
        OpRemoveOrbSlots remove => $".removeOrbSlots {remove.Count}",
        OpAddPlayedCardCombatCost cost => $".addPlayedCardCombatCost {LeanInt(cost.Amount)}",
        OpDealDamageValue d => $".dealDamageValue {LeanTarget(d.Target)} {LeanRuntimeValue(d.Value)} {d.Hits} {LeanDmgProps(d.Props)}",
        OpGainBlockValue b => $".gainBlockValue {LeanTarget(b.Target)} {LeanRuntimeValue(b.Value)} {LeanRuntimeBlockProps(b.Props)}",
        OpGainCurrentEnergy => ".gainCurrentEnergy",
        OpApplyPowerIfPresent p => $".applyPowerIfPresent {LeanTarget(p.Target)} ({LeanPowerTemplate(p.Power)}) {LeanDec(p.Amount)}",
        OpDealDamageIfPower d => $".dealDamageIfPower {LeanTarget(d.Target)} (ModelId.mkPower {LeanStr(d.HitCount.Power.EntryId)}) {LeanDec(d.Amount)} {d.HitCount.Present} {d.HitCount.Otherwise} {LeanDmgProps(d.Props)}",
        OpDrawIfNoAttacks dr => $".drawIfNoAttacks {dr.Count}",
        _ => throw new InvalidOperationException($"Unexpected IrOp {op}")
    };

    private static string LeanOpList(List<IrOp> ops) =>
        ops.Count == 0 ? "[]" : "[ " + string.Join(", ", ops.Select(LeanOp)) + " ]";

    private static void WriteTypesLean(string path)
    {
        var sb = new StringBuilder();
        sb.AppendLine("/-");
        sb.AppendLine("  AUTO-GENERATED by `tools/Sts2AstExtractor` (Roslyn AST extractor).");
        sb.AppendLine("  Tier-2 generated EffectIR table types, MonsterBlueprint converter,");
        sb.AppendLine("  and decidable well-formedness checkers (zero `sorry`, zero `native_decide`).");
        sb.AppendLine("-/");
        sb.AppendLine("import Sts2Model.Sim.EffectIR");
        sb.AppendLine();
        sb.AppendLine("namespace Sts2Model.Sim.Generated");
        sb.AppendLine();
        sb.AppendLine("open Sts2Model.Core");
        sb.AppendLine("open Sts2Model.Model");
        sb.AppendLine("open Sts2Model.Combat");
        sb.AppendLine("open Sts2Model.Sim");
        sb.AppendLine();
        sb.AppendLine("/-- Helper constructor for generated canonical PowerInstance templates. -/");
        sb.AppendLine("@[inline] def mkGenPower (entry : String) (pType : PowerType) (sType : PowerStackType)");
        sb.AppendLine("    (iType : PowerInstanceType) (allowNeg : Bool) : PowerInstance :=");
        sb.AppendLine("  { instanceId := 0, modelId := ModelId.mkPower entry, ownerId := 0");
        sb.AppendLine("  , powerType := pType, stackType := sType, instanceType := iType");
        sb.AppendLine("  , allowNegative := allowNeg, amount := 1 }");
        sb.AppendLine();
        sb.AppendLine("structure GeneratedCardEntry where");
        sb.AppendLine("  id          : String");
        sb.AppendLine("  baseOps     : EffectProgram");
        sb.AppendLine("  upgradedOps : EffectProgram");
        sb.AppendLine("  deriving Repr, DecidableEq");
        sb.AppendLine();
        sb.AppendLine("structure GeneratedPotionEntry where");
        sb.AppendLine("  id  : String");
        sb.AppendLine("  ops : EffectProgram");
        sb.AppendLine("  deriving Repr, DecidableEq");
        sb.AppendLine();
        sb.AppendLine("structure GeneratedMonsterNode where");
        sb.AppendLine("  id              : String");
        sb.AppendLine("  followUpId      : String := \"\"");
        sb.AppendLine("  isRandomBranch  : Bool := false");
        sb.AppendLine("  randomTargets   : List (String × Nat) := []");
        sb.AppendLine("  mustPerformOnce : Bool := false");
        sb.AppendLine("  deriving Repr, DecidableEq");
        sb.AppendLine();
        sb.AppendLine("structure GeneratedMonsterMove where");
        sb.AppendLine("  moveId : String");
        sb.AppendLine("  ops    : EffectProgram");
        sb.AppendLine("  deriving Repr, DecidableEq");
        sb.AppendLine();
        sb.AppendLine("structure GeneratedMonsterEntry where");
        sb.AppendLine("  id             : String");
        sb.AppendLine("  initialStateId : String");
        sb.AppendLine("  nodes          : List GeneratedMonsterNode");
        sb.AppendLine("  moves          : List GeneratedMonsterMove");
        sb.AppendLine("  deriving Repr, DecidableEq");
        sb.AppendLine();
        sb.AppendLine("def toMonsterBlueprint (m : GeneratedMonsterEntry) : MonsterBlueprint :=");
        sb.AppendLine("  { modelId := ModelId.mkMonster m.id");
        sb.AppendLine("  , stateMachine :=");
        sb.AppendLine("      { initialStateId := m.initialStateId");
        sb.AppendLine("      , currentStateId := m.initialStateId");
        sb.AppendLine("      , nodes := fun sid =>");
        sb.AppendLine("          match m.nodes.find? (·.id == sid) with");
        sb.AppendLine("          | none => none");
        sb.AppendLine("          | some n =>");
        sb.AppendLine("              let kind : MonsterStateKind :=");
        sb.AppendLine("                if n.isRandomBranch then .randomBranch n.randomTargets");
        sb.AppendLine("                else .move n.followUpId true n.mustPerformOnce");
        sb.AppendLine("              some { id := n.id, kind := kind, shouldAppearInLogs := !n.isRandomBranch } }");
        sb.AppendLine("  , moveEffects := fun mid =>");
        sb.AppendLine("      match m.moves.find? (·.moveId == mid) with");
        sb.AppendLine("      | some mv => mv.ops");
        sb.AppendLine("      | none => [] }");
        sb.AppendLine();
        sb.AppendLine("/-- Decidable structural well-formedness check for generated card entries. -/");
        sb.AppendLine("def cardEntryWellFormed (c : GeneratedCardEntry) : Bool :=");
        sb.AppendLine("  !c.id.isEmpty && (!c.baseOps.isEmpty || !c.upgradedOps.isEmpty)");
        sb.AppendLine();
        sb.AppendLine("/-- Decidable structural well-formedness check for generated potion entries. -/");
        sb.AppendLine("def potionEntryWellFormed (p : GeneratedPotionEntry) : Bool :=");
        sb.AppendLine("  !p.id.isEmpty && !p.ops.isEmpty");
        sb.AppendLine();
        sb.AppendLine("/-- Decidable structural well-formedness check for generated monster blueprints. -/");
        sb.AppendLine("def monsterEntryWellFormed (m : GeneratedMonsterEntry) : Bool :=");
        sb.AppendLine("  let hasNode (sid : String) : Bool := m.nodes.any (·.id == sid)");
        sb.AppendLine("  let hasMove (mid : String) : Bool := m.moves.any (·.moveId == mid)");
        sb.AppendLine("  !m.id.isEmpty && !m.initialStateId.isEmpty && hasNode m.initialStateId &&");
        sb.AppendLine("  m.nodes.all fun n =>");
        sb.AppendLine("    if n.isRandomBranch then");
        sb.AppendLine("      !n.randomTargets.isEmpty && n.randomTargets.all (fun (tid, w) => hasNode tid && w > 0)");
        sb.AppendLine("    else");
        sb.AppendLine("      hasMove n.id && (n.followUpId.isEmpty || hasNode n.followUpId)");
        sb.AppendLine();
        sb.AppendLine("end Sts2Model.Sim.Generated");
        File.WriteAllText(path, sb.ToString());
    }

    private static List<List<T>> Chunk<T>(List<T> items, int size)
    {
        var chunks = new List<List<T>>();
        for (int i = 0; i < items.Count; i += size)
            chunks.Add(items.GetRange(i, Math.Min(size, items.Count - i)));
        if (chunks.Count == 0) chunks.Add(new List<T>());
        return chunks;
    }

    private static string JoinChunksRight(string prefix, int start, int count)
    {
        if (start >= count - 1) return $"{prefix}Chunk{start}";
        return $"{prefix}Chunk{start} ++ ({JoinChunksRight(prefix, start + 1, count)})";
    }

    private static void WriteCardsLean(string path, List<ExtractedCard> cards)
    {
        var chunks = Chunk(cards, ChunkSize);
        var sb = new StringBuilder();
        sb.AppendLine("/-");
        sb.AppendLine($"  AUTO-GENERATED by `tools/Sts2AstExtractor` ({cards.Count} vanilla Cards, {chunks.Count} sorted chunks).");
        sb.AppendLine("-/");
        sb.AppendLine("import Sts2Model.Sim.Generated.Types");
        sb.AppendLine();
        sb.AppendLine("namespace Sts2Model.Sim.Generated");
        sb.AppendLine("open Sts2Model.Core Sts2Model.Model Sts2Model.Sim");
        sb.AppendLine();
        for (int ci = 0; ci < chunks.Count; ci++)
        {
            sb.AppendLine($"def cardsChunk{ci} : List GeneratedCardEntry := [");
            for (int i = 0; i < chunks[ci].Count; i++)
            {
                var c = chunks[ci][i];
                string comma = i + 1 < chunks[ci].Count ? "," : "";
                sb.AppendLine($"  {{ id := {LeanStr(c.EntryId)}, baseOps := {LeanOpList(c.BaseOps)}, upgradedOps := {LeanOpList(c.UpgradedOps)} }}{comma}");
            }
            sb.AppendLine("]");
            sb.AppendLine();
        }
        sb.AppendLine("def allGeneratedCards : List GeneratedCardEntry :=");
        sb.AppendLine($"  {JoinChunksRight("cards", 0, chunks.Count)}");
        sb.AppendLine();
        sb.AppendLine("end Sts2Model.Sim.Generated");
        File.WriteAllText(path, sb.ToString());
    }

    private static void WritePotionsLean(string path, List<ExtractedPotion> potions)
    {
        var chunks = Chunk(potions, ChunkSize);
        var sb = new StringBuilder();
        sb.AppendLine("/-");
        sb.AppendLine($"  AUTO-GENERATED by `tools/Sts2AstExtractor` ({potions.Count} vanilla Potions, {chunks.Count} sorted chunks).");
        sb.AppendLine("-/");
        sb.AppendLine("import Sts2Model.Sim.Generated.Types");
        sb.AppendLine();
        sb.AppendLine("namespace Sts2Model.Sim.Generated");
        sb.AppendLine("open Sts2Model.Core Sts2Model.Model Sts2Model.Sim");
        sb.AppendLine();
        for (int ci = 0; ci < chunks.Count; ci++)
        {
            sb.AppendLine($"def potionsChunk{ci} : List GeneratedPotionEntry := [");
            for (int i = 0; i < chunks[ci].Count; i++)
            {
                var p = chunks[ci][i];
                string comma = i + 1 < chunks[ci].Count ? "," : "";
                sb.AppendLine($"  {{ id := {LeanStr(p.EntryId)}, ops := {LeanOpList(p.Ops)} }}{comma}");
            }
            sb.AppendLine("]");
            sb.AppendLine();
        }
        sb.AppendLine("def allGeneratedPotions : List GeneratedPotionEntry :=");
        sb.AppendLine($"  {JoinChunksRight("potions", 0, chunks.Count)}");
        sb.AppendLine();
        sb.AppendLine("end Sts2Model.Sim.Generated");
        File.WriteAllText(path, sb.ToString());
    }

    private static void WriteMonstersLean(string path, List<ExtractedMonster> monsters)
    {
        var chunks = Chunk(monsters, ChunkSize);
        var sb = new StringBuilder();
        sb.AppendLine("/-");
        sb.AppendLine($"  AUTO-GENERATED by `tools/Sts2AstExtractor` ({monsters.Count} vanilla Monsters, {chunks.Count} sorted chunks).");
        sb.AppendLine("-/");
        sb.AppendLine("import Sts2Model.Sim.Generated.Types");
        sb.AppendLine();
        sb.AppendLine("namespace Sts2Model.Sim.Generated");
        sb.AppendLine("open Sts2Model.Core Sts2Model.Model Sts2Model.Sim");
        sb.AppendLine();
        for (int ci = 0; ci < chunks.Count; ci++)
        {
            sb.AppendLine($"def monstersChunk{ci} : List GeneratedMonsterEntry := [");
            for (int i = 0; i < chunks[ci].Count; i++)
            {
                var m = chunks[ci][i];
                string comma = i + 1 < chunks[ci].Count ? "," : "";
                string nodesStr = "[ " + string.Join(", ", m.Nodes.Select(n =>
                {
                    string rtStr = n.RandomTargets.Count == 0
                        ? "[]"
                        : "[ " + string.Join(", ", n.RandomTargets.Select(rt => $"({LeanStr(rt.TargetId)}, {rt.Weight})")) + " ]";
                    return $"{{ id := {LeanStr(n.Id)}, followUpId := {LeanStr(n.FollowUpId)}, isRandomBranch := {(n.IsRandomBranch ? "true" : "false")}, randomTargets := {rtStr}, mustPerformOnce := {(n.MustPerformOnce ? "true" : "false")} }}";
                })) + " ]";
                string movesStr = "[ " + string.Join(", ", m.Moves.Select(mv =>
                    $"{{ moveId := {LeanStr(mv.MoveId)}, ops := {LeanOpList(mv.Ops)} }}")) + " ]";
                sb.AppendLine($"  {{ id := {LeanStr(m.EntryId)}, initialStateId := {LeanStr(m.InitialStateId)}, nodes := {nodesStr}, moves := {movesStr} }}{comma}");
            }
            sb.AppendLine("]");
            sb.AppendLine();
        }
        sb.AppendLine("def allGeneratedMonsters : List GeneratedMonsterEntry :=");
        sb.AppendLine($"  {JoinChunksRight("monsters", 0, chunks.Count)}");
        sb.AppendLine();
        sb.AppendLine("end Sts2Model.Sim.Generated");
        File.WriteAllText(path, sb.ToString());
    }

    private static void EmitVerifySection(
        StringBuilder sb,
        string prefix,
        string allName,
        string wfPred,
        int chunkCount,
        List<int> chunkLens,
        int totalCount)
    {
        for (int i = 0; i < chunkCount; i++)
        {
            sb.AppendLine($"private theorem {prefix}Chunk{i}_len : {prefix}Chunk{i}.length = {chunkLens[i]} := rfl");
            sb.AppendLine($"private theorem {prefix}Chunk{i}_sorted : isStrictlySorted ({prefix}Chunk{i}.map (·.id)) = true := by decide");
            sb.AppendLine($"private theorem {prefix}Chunk{i}_wf : {prefix}Chunk{i}.all {wfPred} = true := by decide");
        }
        sb.AppendLine();
        int last = chunkCount - 1;
        sb.AppendLine($"private theorem {prefix}Suffix{last}_sorted : isStrictlySorted ({prefix}Chunk{last}.map (·.id)) = true := {prefix}Chunk{last}_sorted");
        for (int i = last - 1; i >= 0; i--)
        {
            string expr = JoinChunksRight(prefix, i, chunkCount);
            sb.AppendLine($"private theorem {prefix}Suffix{i}_sorted : isStrictlySorted (({expr}).map (·.id)) = true := by");
            sb.AppendLine($"  apply strictlySorted_join _ _ _ {prefix}Chunk{i}_sorted {prefix}Suffix{i + 1}_sorted");
            sb.AppendLine($"  decide");
        }
        sb.AppendLine();
        sb.AppendLine($"private theorem {prefix}Suffix{last}_wf : {prefix}Chunk{last}.all {wfPred} = true := {prefix}Chunk{last}_wf");
        for (int i = last - 1; i >= 0; i--)
        {
            string expr = JoinChunksRight(prefix, i, chunkCount);
            sb.AppendLine($"private theorem {prefix}Suffix{i}_wf : ({expr}).all {wfPred} = true := by");
            sb.AppendLine($"  rw [List.all_append, {prefix}Chunk{i}_wf, {prefix}Suffix{i + 1}_wf]; rfl");
        }
        sb.AppendLine();
        if (chunkCount == 1)
        {
            sb.AppendLine($"theorem {allName}_length : {allName}.length = {totalCount} :=");
            sb.AppendLine($"  {prefix}Chunk0_len");
        }
        else
        {
            sb.AppendLine($"theorem {allName}_length : {allName}.length = {totalCount} := by");
            string lenRewrites = string.Join(", ", Enumerable.Range(0, chunkCount).Select(i => $"{prefix}Chunk{i}_len"));
            sb.AppendLine($"  simp only [{allName}, List.length_append, {lenRewrites}]");
        }
        sb.AppendLine();
        sb.AppendLine($"theorem {allName}_nodup : ({allName}.map (·.id)).Nodup :=");
        sb.AppendLine($"  isStrictlySorted_implies_nodup _ {prefix}Suffix0_sorted");
        sb.AppendLine();
        sb.AppendLine($"theorem {allName}_wellFormed : {allName}.all {wfPred} = true :=");
        sb.AppendLine($"  {prefix}Suffix0_wf");
        sb.AppendLine();
    }

    private static void WriteVerifyLean(
        string path,
        List<ExtractedCard> cards,
        List<ExtractedPotion> potions,
        List<ExtractedMonster> monsters)
    {
        var cChunks = Chunk(cards, ChunkSize);
        var pChunks = Chunk(potions, ChunkSize);
        var mChunks = Chunk(monsters, ChunkSize);

        var sb = new StringBuilder();
        sb.AppendLine("/-");
        sb.AppendLine("  AUTO-GENERATED by `tools/Sts2AstExtractor`.");
        sb.AppendLine($"  Pure kernel-checked count, ID uniqueness (`Nodup`), and structural well-formedness");
        sb.AppendLine($"  proofs for Tier-2 Cards ({cards.Count}), Potions ({potions.Count}), and Monsters ({monsters.Count}).");
        sb.AppendLine("  Uses ZERO `sorry`, ZERO `axiom`, and ZERO `native_decide`.");
        sb.AppendLine("-/");
        sb.AppendLine("import Sts2Model.Catalog.Types");
        sb.AppendLine("import Sts2Model.Sim.Generated.Types");
        sb.AppendLine("import Sts2Model.Sim.Generated.Cards");
        sb.AppendLine("import Sts2Model.Sim.Generated.Potions");
        sb.AppendLine("import Sts2Model.Sim.Generated.Monsters");
        sb.AppendLine();
        sb.AppendLine("namespace Sts2Model.Sim.Generated");
        sb.AppendLine();
        sb.AppendLine("open Sts2Model.Catalog");
        sb.AppendLine("open Sts2Model.Sim");
        sb.AppendLine();
        EmitVerifySection(sb, "cards", "allGeneratedCards", "cardEntryWellFormed",
            cChunks.Count, cChunks.Select(c => c.Count).ToList(), cards.Count);
        EmitVerifySection(sb, "potions", "allGeneratedPotions", "potionEntryWellFormed",
            pChunks.Count, pChunks.Select(c => c.Count).ToList(), potions.Count);
        EmitVerifySection(sb, "monsters", "allGeneratedMonsters", "monsterEntryWellFormed",
            mChunks.Count, mChunks.Select(c => c.Count).ToList(), monsters.Count);

        sb.AppendLine("/-- Lookup Tier-2 extracted card effect program by model entry ID and upgrade flag. -/");
        sb.AppendLine("def lookupGeneratedCard (entry : String) (upgraded : Bool) : Option EffectProgram :=");
        sb.AppendLine("  match allGeneratedCards.find? (·.id == entry) with");
        sb.AppendLine("  | none => none");
        sb.AppendLine("  | some c => some (if upgraded then c.upgradedOps else c.baseOps)");
        sb.AppendLine();
        sb.AppendLine("/-- Lookup Tier-2 extracted potion effect program by model entry ID. -/");
        sb.AppendLine("def lookupGeneratedPotion (entry : String) : Option EffectProgram :=");
        sb.AppendLine("  (allGeneratedPotions.find? (·.id == entry)).map (·.ops)");
        sb.AppendLine();
        sb.AppendLine("/-- Lookup Tier-2 extracted monster AI blueprint by model entry ID. -/");
        sb.AppendLine("def lookupGeneratedMonster (entry : String) : Option MonsterBlueprint :=");
        sb.AppendLine("  (allGeneratedMonsters.find? (·.id == entry)).map toMonsterBlueprint");
        sb.AppendLine();
        sb.AppendLine("end Sts2Model.Sim.Generated");
        File.WriteAllText(path, sb.ToString());
    }

    private static string CsStr(string s) => "\"" + s.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\"";

    private static string CsKind(IrKind kind) => $"nameof(IrKind.{kind})";
    private static string CsBool(bool b) => b ? "true" : "false";
    private static string CsDecimal(decimal value) => value.ToString(CultureInfo.InvariantCulture) + "m";

    private static string CsFlatOp(IrKind kind, int count) =>
        $"new T2Op({CsKind(kind)}, \"Self\", {CsDecimal(count)})";

    private static string CsValueOp(IrKind kind, IrTarget target, RuntimeValue value, int hits, IrProps props) =>
        $"new T2Op({CsKind(kind)}, {CsStr(target.ToString())}, {CsDecimal(value.Base)}, {hits}, " +
        $"{CsBool(props.Unpowered)}, {CsBool(props.Unblockable)}, {CsBool(props.IsCard)}, {CsStr(RuntimeValueName(value.Source))}, " +
        $"Move: {CsBool(props.Move)}, Multiplier: {CsDecimal(value.Multiplier)})";

    private static string CsOp(IrOp op) => op switch
    {
        OpDealDamage d => $"new T2Op(\"dealDamage\", {CsStr(d.Target.ToString())}, {d.Amount.ToString(CultureInfo.InvariantCulture)}m, {d.Hits}, {(d.Props.Unpowered ? "true" : "false")}, {(d.Props.Unblockable ? "true" : "false")}, {(d.Props.IsCard ? "true" : "false")}{(d.Props.Move ? "" : ", Move: false")})",
        OpGainBlock b => $"new T2Op(\"gainBlock\", {CsStr(b.Target.ToString())}, {b.Amount.ToString(CultureInfo.InvariantCulture)}m, 1, {(b.Props.Unpowered ? "true" : "false")}, false, {(b.Props.IsCard ? "true" : "false")})",
        OpApplyPower p => $"new T2Op(\"applyPower\", {CsStr(p.Target.ToString())}, {p.Amount.ToString(CultureInfo.InvariantCulture)}m, 1, false, false, false, {CsStr(p.Power.EntryId)}, {(p.Power.PowerType == "debuff" ? "true" : "false")}, {(p.Power.AllowNegative ? "true" : "false")}, {(p.Power.StackType == "single" ? "true" : "false")})",
        OpRemovePower r => $"new T2Op(\"removePower\", {CsStr(r.Target.ToString())}, 0m, 1, false, false, false, {CsStr(r.PowerEntryId)})",
        OpDraw dr => $"new T2Op(\"draw\", \"Self\", {dr.Count}m)",
        OpDiscardChosen dc => $"new T2Op(\"discardChosen\", \"Self\", {dc.Count}m, {dc.ChoiceId})",
        OpDiscardAllHand => "new T2Op(\"discardAllHand\", \"Self\", 0m)",
        OpExhaustSelf => "new T2Op(\"exhaustSelf\", \"Self\", 0m)",
        OpExhaustChosen ec => $"new T2Op(\"exhaustChosen\", \"Self\", {ec.Count}m, {ec.ChoiceId})",
        OpGainEnergy ge => $"new T2Op(\"gainEnergy\", \"Self\", {ge.Amount}m)",
        OpGainStars gs => $"new T2Op(\"gainStars\", \"Self\", {gs.Amount}m)",
        OpHeal h => $"new T2Op(\"heal\", {CsStr(h.Target.ToString())}, {h.Amount.ToString(CultureInfo.InvariantCulture)}m)",
        OpChannelOrb o => $"new T2Op(\"channelOrb\", \"Self\", 0m, 1, false, false, false, {CsStr(o.Kind.ToString().ToLowerInvariant())})",
        OpEvokeOrb e => $"new T2Op(\"evokeOrb\", \"Self\", {e.Times}m)",
        OpForge f => $"new T2Op(\"forge\", \"Self\", {f.Amount.ToString(CultureInfo.InvariantCulture)}m)",
        OpAddGeneratedCard g => $"new T2Op(\"addGeneratedCard\", {CsStr(g.Pile)}, {g.Count}m, {g.Cost}, false, false, false, {CsStr(g.CardEntry)}, false, false, false, {CsStr(g.CardType)}, {CsStr(g.Pos)})",
        OpSummonOsty s => $"new T2Op(\"summonOsty\", \"Self\", {s.Amount.ToString(CultureInfo.InvariantCulture)}m)",
        OpDealDamageAsc d => $"new T2Op(\"dealDamageAsc\", {CsStr(d.Target.ToString())}, {d.Amt.BaseValue}m, {d.Hits}, {(d.Props.Unpowered ? "true" : "false")}, {(d.Props.Unblockable ? "true" : "false")}, false, \"\", false, false, false, \"\", \"\", {d.Amt.Threshold}, {d.Amt.AscValue}{(d.Props.Move ? "" : ", Move: false")})",
        OpGainBlockAsc b => $"new T2Op(\"gainBlockAsc\", {CsStr(b.Target.ToString())}, {b.Amt.BaseValue}m, 1, {(b.Props.Unpowered ? "true" : "false")}, false, false, \"\", false, false, false, \"\", \"\", {b.Amt.Threshold}, {b.Amt.AscValue})",
        OpApplyPowerAsc p => $"new T2Op(\"applyPowerAsc\", {CsStr(p.Target.ToString())}, {p.Amt.BaseValue}m, 1, false, false, false, {CsStr(p.Power.EntryId)}, {(p.Power.PowerType == "debuff" ? "true" : "false")}, {(p.Power.AllowNegative ? "true" : "false")}, {(p.Power.StackType == "single" ? "true" : "false")}, \"\", \"\", {p.Amt.Threshold}, {p.Amt.AscValue})",
        OpAddOrbSlots add => CsFlatOp(IrKind.AddOrbSlots, add.Count),
        OpRemoveOrbSlots remove => CsFlatOp(IrKind.RemoveOrbSlots, remove.Count),
        OpAddPlayedCardCombatCost cost => CsFlatOp(IrKind.AddPlayedCardCombatCost, cost.Amount),
        OpDealDamageValue d => CsValueOp(IrKind.DealDamageValue, d.Target, d.Value, d.Hits, d.Props),
        OpGainBlockValue b => CsValueOp(IrKind.GainBlockValue, b.Target, b.Value, 1, b.Props),
        OpGainCurrentEnergy => CsFlatOp(IrKind.GainCurrentEnergy, 0),
        OpApplyPowerIfPresent p => $"new T2Op({CsKind(IrKind.ApplyPowerIfPresent)}, {CsStr(p.Target.ToString())}, {CsDecimal(p.Amount)}, " +
            $"StrArg: {CsStr(p.Power.EntryId)}, IsDebuff: {CsBool(p.Power.PowerType == "debuff")}, " +
            $"AllowNeg: {CsBool(p.Power.AllowNegative)}, IsSingle: {CsBool(p.Power.StackType == "single")})",
        OpDealDamageIfPower d => $"new T2Op({CsKind(IrKind.DealDamageIfPower)}, {CsStr(d.Target.ToString())}, {CsDecimal(d.Amount)}, " +
            $"{d.HitCount.Present}, {CsBool(d.Props.Unpowered)}, {CsBool(d.Props.Unblockable)}, {CsBool(d.Props.IsCard)}, " +
            $"{CsStr(d.HitCount.Power.EntryId)}, Move: {CsBool(d.Props.Move)}, Param2: {d.HitCount.Otherwise})",
        OpDrawIfNoAttacks dr => CsFlatOp(IrKind.DrawIfNoAttacks, dr.Count),
        _ => throw new InvalidOperationException($"Unexpected IrOp {op}")
    };

    private static void WriteTier2OracleDataCs(
        string path,
        List<ExtractedCard> cards,
        List<ExtractedPotion> potions,
        List<ExtractedMonster> monsters)
    {
        var sb = new StringBuilder();
        sb.AppendLine("// AUTO-GENERATED by `tools/Sts2AstExtractor` — DO NOT EDIT MANUALLY.");
        sb.AppendLine("// Static C# lookup tables mirroring `Sts2Model/Sim/Generated/*.lean` for Tier-2 differential testing.");
        sb.AppendLine("using System;");
        sb.AppendLine("using System.Collections.Generic;");
        sb.AppendLine();
        sb.AppendLine($"internal enum IrKind {{ {string.Join(", ", Enum.GetNames<IrKind>())} }}");
        sb.AppendLine();
        sb.AppendLine("internal sealed record T2Op(");
        sb.AppendLine("    string Kind,");
        sb.AppendLine("    string Target,");
        sb.AppendLine("    decimal Amount,");
        sb.AppendLine("    int Param1 = 1,");
        sb.AppendLine("    bool Unpowered = false,");
        sb.AppendLine("    bool Unblockable = false,");
        sb.AppendLine("    bool FromCard = false,");
        sb.AppendLine("    string StrArg = \"\",");
        sb.AppendLine("    bool IsDebuff = false,");
        sb.AppendLine("    bool AllowNeg = false,");
        sb.AppendLine("    bool IsSingle = false,");
        sb.AppendLine("    string StrArg2 = \"\",");
        sb.AppendLine("    string StrArg3 = \"\",");
        sb.AppendLine("    int AscThreshold = 0,");
        sb.AppendLine("    int AscValue = 0,");
        sb.AppendLine("    bool Move = true,");
        sb.AppendLine("    decimal Multiplier = 0m,");
        sb.AppendLine("    int Param2 = 1);");
        sb.AppendLine();
        sb.AppendLine("internal sealed record T2Card(string Id, T2Op[] BaseOps, T2Op[] UpgradedOps);");
        sb.AppendLine("internal sealed record T2Potion(string Id, T2Op[] Ops);");
        sb.AppendLine("internal sealed record T2MonsterNode(string Id, string FollowUpId, bool IsRandomBranch, (string TargetId, int Weight)[] RandomTargets, bool MustPerformOnce);");
        sb.AppendLine("internal sealed record T2MonsterMove(string MoveId, T2Op[] Ops);");
        sb.AppendLine("internal sealed record T2Monster(string Id, string InitialStateId, T2MonsterNode[] Nodes, T2MonsterMove[] Moves);");
        sb.AppendLine();
        sb.AppendLine("internal static class Tier2OracleData");
        sb.AppendLine("{");
        sb.AppendLine("    public static readonly Dictionary<string, T2Card> Cards = new(StringComparer.Ordinal)");
        sb.AppendLine("    {");
        foreach (var c in cards)
        {
            string bOps = string.Join(", ", c.BaseOps.Select(CsOp));
            string uOps = string.Join(", ", c.UpgradedOps.Select(CsOp));
            sb.AppendLine($"        [{CsStr(c.EntryId)}] = new T2Card({CsStr(c.EntryId)}, new T2Op[] {{ {bOps} }}, new T2Op[] {{ {uOps} }}),");
        }
        sb.AppendLine("    };");
        sb.AppendLine();
        sb.AppendLine("    public static readonly Dictionary<string, T2Potion> Potions = new(StringComparer.Ordinal)");
        sb.AppendLine("    {");
        foreach (var p in potions)
        {
            string pOps = string.Join(", ", p.Ops.Select(CsOp));
            sb.AppendLine($"        [{CsStr(p.EntryId)}] = new T2Potion({CsStr(p.EntryId)}, new T2Op[] {{ {pOps} }}),");
        }
        sb.AppendLine("    };");
        sb.AppendLine();
        sb.AppendLine("    public static readonly Dictionary<string, T2Monster> Monsters = new(StringComparer.Ordinal)");
        sb.AppendLine("    {");
        foreach (var m in monsters)
        {
            string nArr = string.Join(", ", m.Nodes.Select(n =>
            {
                string rt = string.Join(", ", n.RandomTargets.Select(t => $"({CsStr(t.TargetId)}, {t.Weight})"));
                return $"new T2MonsterNode({CsStr(n.Id)}, {CsStr(n.FollowUpId)}, {(n.IsRandomBranch ? "true" : "false")}, new (string, int)[] {{ {rt} }}, {(n.MustPerformOnce ? "true" : "false")})";
            }));
            string mvArr = string.Join(", ", m.Moves.Select(mv =>
                $"new T2MonsterMove({CsStr(mv.MoveId)}, new T2Op[] {{ {string.Join(", ", mv.Ops.Select(CsOp))} }})"));
            sb.AppendLine($"        [{CsStr(m.EntryId)}] = new T2Monster({CsStr(m.EntryId)}, {CsStr(m.InitialStateId)}, new T2MonsterNode[] {{ {nArr} }}, new T2MonsterMove[] {{ {mvArr} }}),");
        }
        sb.AppendLine("    };");
        sb.AppendLine("}");
        File.WriteAllText(path, sb.ToString());
    }

    private static void WriteCardManifest(string path, List<ExtractedCard> cards,
        Dictionary<string, CardMeta> cardMetas, List<SkipRecord> skips)
    {
        var generated = cards.ToDictionary(c => c.EntryId, StringComparer.Ordinal);
        var skipped = skips.Where(s => s.Category == "Card").ToDictionary(s => s.EntryId, StringComparer.Ordinal);
        var inventory = cardMetas.Values.OrderBy(m => m.EntryId, StringComparer.Ordinal).ToArray();
        if (generated.Count + skipped.Count != inventory.Length)
            throw new InvalidOperationException("Card inventory does not match the extraction partition");

        using var output = new StreamWriter(path) { NewLine = "\n" };
        output.WriteLine("[");
        for (int i = 0; i < inventory.Length; i++)
        {
            var m = inventory[i];
            if ((i > 0 && inventory[i - 1].EntryId == m.EntryId) ||
                generated.TryGetValue(m.EntryId, out var card) == skipped.TryGetValue(m.EntryId, out var skip))
                throw new InvalidOperationException($"Expected exactly one extraction result for card {m.EntryId}");

            var metadata = new
            {
                baseCost = m.BaseCost,
                costsX = m.CostsX,
                baseStarCost = m.BaseStarCost,
                cardType = m.CardType,
                rarity = m.Rarity,
                targetType = m.TargetType,
                keywords = m.Keywords,
                tags = m.Tags
            };
            const string sourceDir = "reference/sts2/MegaCrit.Sts2.Core.Models.Cards/";
            string entry;
            if (card != null)
            {
                entry = JsonSerializer.Serialize(new
                {
                    id = m.EntryId,
                    source = sourceDir + card.FileName,
                    status = "generated",
                    metadata,
                    upgradedMetadata = new { cost = card.Upgrade.Cost, starCost = m.BaseStarCost, keywords = card.Upgrade.Keywords },
                    baseOps = card.BaseOps.Select(LeanOp).ToArray(),
                    upgradedOps = card.UpgradedOps.Select(LeanOp).ToArray()
                });
            }
            else
            {
                var position = skip!.Position ?? throw new InvalidOperationException($"Missing skip location for {m.EntryId}");
                entry = JsonSerializer.Serialize(new
                {
                    id = m.EntryId,
                    source = sourceDir + skip.FileName,
                    status = "skipped",
                    metadata,
                    reason = new
                    {
                        code = skip.Reason,
                        location = new { line = position.Line + 1, column = position.Character + 1 },
                        detail = skip.Detail
                    }
                });
            }
            output.Write("  ");
            output.Write(entry);
            output.WriteLine(i + 1 == inventory.Length ? "" : ",");
        }
        output.WriteLine("]");
    }

    private static void WriteAuditMarkdown(
        string path,
        List<ExtractedCard> cards,
        List<ExtractedPotion> potions,
        List<ExtractedMonster> monsters,
        List<SkipRecord> skips)
    {
        int cardSkips = skips.Count(s => s.Category == "Card");
        int potionSkips = skips.Count(s => s.Category == "Potion");
        int monsterSkips = skips.Count(s => s.Category == "Monster");

        var sb = new StringBuilder();
        sb.AppendLine("# Tier-2 Roslyn AST Extraction Audit Report");
        sb.AppendLine();
        sb.AppendLine("> Auto-generated by `tools/Sts2AstExtractor`. Unknown statements, unsupported calculated");
        sb.AppendLine("> values, and unsupported control flow are rejected explicitly. Counts are not a game-equivalence claim.");
        sb.AppendLine("> [Card manifest](tier2_cards.json) records source locations, variant metadata, and programs.");
        sb.AppendLine();
        sb.AppendLine("From the repository root, run `dotnet run --project tools/Sts2AstExtractor -- .` to regenerate,");
        sb.AppendLine("then `uv run python scripts/check_tier2_cards.py` to reconcile with the independent catalog parser.");
        sb.AppendLine("For a version comparison, keep the previous JSON and pass it with `--compare PREVIOUS_JSON` after regenerating.");
        sb.AppendLine();
        sb.AppendLine("## Coverage Summary");
        sb.AppendLine();
        sb.AppendLine("| Category | Total Evaluated | Extracted | Explicitly Skipped | Coverage |");
        sb.AppendLine("|---|---:|---:|---:|---:|");
        sb.AppendLine($"| Cards | {cards.Count + cardSkips} | {cards.Count} | {cardSkips} | {100.0 * cards.Count / Math.Max(1, cards.Count + cardSkips):F1}% |");
        sb.AppendLine($"| Potions | {potions.Count + potionSkips} | {potions.Count} | {potionSkips} | {100.0 * potions.Count / Math.Max(1, potions.Count + potionSkips):F1}% |");
        sb.AppendLine($"| Monsters | {monsters.Count + monsterSkips} | {monsters.Count} | {monsterSkips} | {100.0 * monsters.Count / Math.Max(1, monsters.Count + monsterSkips):F1}% |");
        sb.AppendLine();
        sb.AppendLine("## Skip Reason Breakdown");
        sb.AppendLine();
        foreach (string catName in new[] { "Card", "Potion", "Monster" })
        {
            sb.AppendLine($"### {catName}s");
            sb.AppendLine();
            sb.AppendLine("| Skip Reason | Count |");
            sb.AppendLine("|---|---:|");
            foreach (var grp in skips.Where(s => s.Category == catName).GroupBy(s => s.Reason).OrderByDescending(g => g.Count()).ThenBy(g => g.Key, StringComparer.Ordinal))
            {
                sb.AppendLine($"| `{grp.Key}` | {grp.Count()} |");
            }
            sb.AppendLine();
        }
        sb.AppendLine("## Extracted Monsters (Ascension-Parameterized)");
        sb.AppendLine();
        sb.AppendLine("| Monster ID | Initial State | Nodes | Moves |");
        sb.AppendLine("|---|---|---:|---:|");
        foreach (var m in monsters)
        {
            sb.AppendLine($"| `{m.EntryId}` | `{m.InitialStateId}` | {m.Nodes.Count} | {m.Moves.Count} |");
        }
        sb.AppendLine();
        sb.AppendLine("## Itemized Skip Log");
        sb.AppendLine();
        sb.AppendLine("| Category | File | Entry ID | Reason | Detail |");
        sb.AppendLine("|---|---|---|---|---|");
        foreach (var s in skips.OrderBy(x => x.Category, StringComparer.Ordinal).ThenBy(x => x.EntryId, StringComparer.Ordinal))
        {
            string cleanDetail = s.Detail.Replace("|", "\\|").Replace("\r", " ").Replace("\n", " ");
            if (cleanDetail.Length > 120) cleanDetail = cleanDetail[..117] + "...";
            sb.AppendLine($"| {s.Category} | `{s.FileName}` | `{s.EntryId}` | `{s.Reason}` | `{cleanDetail}` |");
        }
        File.WriteAllText(path, sb.ToString());
    }
}
