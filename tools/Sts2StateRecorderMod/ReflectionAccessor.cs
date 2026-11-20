using System;
using System.Collections;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Globalization;
using System.Reflection;
using System.Text;
using System.Text.Json.Nodes;

namespace Sts2StateRecorder;

/// <summary>
/// High-performance cached reflection utilities for inspecting STS2 public and private runtime state
/// without hard binary version coupling to every internal game class.
/// </summary>
internal static class ReflectionAccessor
{
    private const BindingFlags AllInstanceFlags =
        BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic;

    private const BindingFlags AllStaticFlags =
        BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic;

    private const BindingFlags DeclaredInstanceFlags =
        BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly;

    private static readonly ConcurrentDictionary<string, Type?> TypeCache = new();
    private static readonly ConcurrentDictionary<(Type, string), PropertyInfo?> PropCache = new();
    private static readonly ConcurrentDictionary<(Type, string), FieldInfo?> FieldCache = new();
    private static readonly ConcurrentDictionary<(Type, string, int), MethodInfo?> MethodCache = new();
    private static readonly ConcurrentDictionary<Type, FieldInfo[]> DeclaredFieldsCache = new();

    private static readonly HashSet<string> IgnoredCustomFieldNames = new(StringComparer.Ordinal)
    {
        "_canonicalInstance",
        "_resolvedBigIconPath",
        "_titleLocString",
        "_dynamicVars",
        "_owner",
        "_applier",
        "_target",
        "_creature",
        "_player",
        "_runState",
        "_combatState",
        "_logger",
        "_pool",
        "_piles",
        "_runPiles",
        "_allCards",
        "_allies",
        "_enemies",
        "_powers",
        "_relics",
        "_potionSlots",
        "_arrows",
        "_pets",
        "_entries",
        "_completionSource",
        "_pauseForPlayerChoiceTaskSource",
        "_executeAfterResumptionTaskSource",
        "_executionTask",
        "_executionStartedSource",
        "_choiceContextSetSource",
        "debugArtificialDelayAfterTask"
    };

    public static Assembly? FindSts2Assembly()
    {
        foreach (Assembly asm in AppDomain.CurrentDomain.GetAssemblies())
        {
            string? name = asm.GetName().Name;
            if (string.Equals(name, "sts2", StringComparison.OrdinalIgnoreCase))
            {
                return asm;
            }
        }
        return null;
    }

    public static Type? FindType(string fullName)
    {
        return TypeCache.GetOrAdd(fullName, static key =>
        {
            Assembly? sts2Asm = FindSts2Assembly();
            if (sts2Asm != null)
            {
                Type? t = sts2Asm.GetType(key, throwOnError: false);
                if (t != null)
                {
                    return t;
                }
            }
            foreach (Assembly asm in AppDomain.CurrentDomain.GetAssemblies())
            {
                Type? t = asm.GetType(key, throwOnError: false);
                if (t != null)
                {
                    return t;
                }
            }
            return null;
        });
    }

    public static object? GetStaticMember(string typeFullName, string memberName)
    {
        Type? type = FindType(typeFullName);
        if (type == null)
        {
            return null;
        }
        return GetStaticMember(type, memberName);
    }

    public static object? GetStaticMember(Type type, string memberName)
    {
        try
        {
            PropertyInfo? prop = type.GetProperty(memberName, AllStaticFlags);
            if (prop != null)
            {
                return prop.GetValue(null);
            }
            FieldInfo? field = type.GetField(memberName, AllStaticFlags);
            if (field != null)
            {
                return field.GetValue(null);
            }
        }
        catch
        {
            // Ignore reflection access exceptions on uninitialized singletons
        }
        return null;
    }

    public static PropertyInfo? GetPropertyInfo(Type type, string name)
    {
        return PropCache.GetOrAdd((type, name), static key =>
        {
            Type? cur = key.Item1;
            while (cur != null && cur != typeof(object))
            {
                PropertyInfo? p = cur.GetProperty(key.Item2, DeclaredInstanceFlags);
                if (p != null)
                {
                    return p;
                }
                cur = cur.BaseType;
            }
            return key.Item1.GetProperty(key.Item2, AllInstanceFlags);
        });
    }

    public static FieldInfo? GetFieldInfo(Type type, string name)
    {
        return FieldCache.GetOrAdd((type, name), static key =>
        {
            Type? cur = key.Item1;
            while (cur != null && cur != typeof(object))
            {
                FieldInfo? f = cur.GetField(key.Item2, DeclaredInstanceFlags);
                if (f != null)
                {
                    return f;
                }
                cur = cur.BaseType;
            }
            return key.Item1.GetField(key.Item2, AllInstanceFlags);
        });
    }

    public static MethodInfo? GetMethodInfo(Type type, string name, int paramCount = -1)
    {
        return MethodCache.GetOrAdd((type, name, paramCount), static key =>
        {
            Type? cur = key.Item1;
            while (cur != null && cur != typeof(object))
            {
                foreach (MethodInfo m in cur.GetMethods(DeclaredInstanceFlags | AllStaticFlags))
                {
                    if (m.Name == key.Item2 && (key.Item3 < 0 || m.GetParameters().Length == key.Item3))
                    {
                        return m;
                    }
                }
                cur = cur.BaseType;
            }
            return null;
        });
    }

    public static object? GetMember(object? target, string name)
    {
        if (target == null)
        {
            return null;
        }
        Type type = target.GetType();
        try
        {
            PropertyInfo? prop = GetPropertyInfo(type, name);
            if (prop != null && prop.GetIndexParameters().Length == 0)
            {
                return prop.GetValue(target);
            }
            FieldInfo? field = GetFieldInfo(type, name);
            if (field != null)
            {
                return field.GetValue(target);
            }
        }
        catch
        {
            // Ignore getter exceptions (e.g. uninitialized properties that throw InvalidOperationException)
        }
        return null;
    }

    public static object? InvokeMethod(object? target, string methodName, params object?[] args)
    {
        if (target == null)
        {
            return null;
        }
        try
        {
            MethodInfo? method = GetMethodInfo(target.GetType(), methodName, args.Length);
            if (method != null)
            {
                return method.Invoke(target, args);
            }
        }
        catch
        {
            // Ignore invocation exceptions during non-intrusive inspection
        }
        return null;
    }

    public static string? GetString(object? target, string memberName)
    {
        object? val = GetMember(target, memberName);
        return val?.ToString();
    }

    public static int? GetInt(object? target, string memberName)
    {
        object? val = GetMember(target, memberName);
        return val switch
        {
            int i => i,
            uint u => unchecked((int)u),
            short s => s,
            byte b => b,
            long l => (int)l,
            decimal d => (int)d,
            Enum e => Convert.ToInt32(e, CultureInfo.InvariantCulture),
            _ => null
        };
    }

    public static uint? GetUInt(object? target, string memberName)
    {
        object? val = GetMember(target, memberName);
        return val switch
        {
            uint u => u,
            int i when i >= 0 => (uint)i,
            ulong ul => (uint)ul,
            _ => null
        };
    }

    public static ulong? GetULong(object? target, string memberName)
    {
        object? val = GetMember(target, memberName);
        return val switch
        {
            ulong ul => ul,
            long l when l >= 0 => (ulong)l,
            uint u => u,
            int i when i >= 0 => (ulong)i,
            _ => null
        };
    }

    public static bool? GetBool(object? target, string memberName)
    {
        object? val = GetMember(target, memberName);
        return val is bool b ? b : null;
    }

    public static float? GetFloat(object? target, string memberName)
    {
        object? val = GetMember(target, memberName);
        return val switch
        {
            float f => f,
            double d => (float)d,
            decimal m => (float)m,
            _ => null
        };
    }

    public static decimal? GetDecimal(object? target, string memberName)
    {
        object? val = GetMember(target, memberName);
        return val switch
        {
            decimal m => m,
            int i => i,
            long l => l,
            float f => (decimal)f,
            double d => (decimal)d,
            _ => null
        };
    }

    public static string? FormatModelId(object? modelOrId)
    {
        if (modelOrId == null)
        {
            return null;
        }
        Type t = modelOrId.GetType();
        if (t.Name == "ModelId")
        {
            return modelOrId.ToString();
        }
        object? idObj = GetMember(modelOrId, "Id") ?? GetMember(modelOrId, "ModelId");
        return idObj?.ToString();
    }

    public static string? FormatModelEntry(object? modelOrId)
    {
        if (modelOrId == null)
        {
            return null;
        }
        object? idObj = modelOrId.GetType().Name == "ModelId"
            ? modelOrId
            : (GetMember(modelOrId, "Id") ?? GetMember(modelOrId, "ModelId"));
        if (idObj == null)
        {
            return null;
        }
        return GetString(idObj, "Entry") ?? idObj.ToString();
    }

    public static FieldInfo[] GetDeclaredInstanceFields(Type type)
    {
        return DeclaredFieldsCache.GetOrAdd(type, static t => t.GetFields(DeclaredInstanceFlags));
    }

    /// <summary>
    /// Extracts subclass-specific or private runtime fields (e.g. PowerModel._internalData or
    /// custom fields declared on specific CardModel/RelicModel/PowerModel/MonsterModel subclasses),
    /// filtering out UI/Godot/Task/Delegate references and preventing reference cycles.
    /// </summary>
    public static JsonObject? InspectCustomDeclaredFields(object? instance, Type? stopAtBaseType, int maxDepth = 2)
    {
        if (instance == null || maxDepth < 0)
        {
            return null;
        }
        JsonObject result = new();
        Type? cur = instance.GetType();
        while (cur != null && cur != typeof(object) && cur != stopAtBaseType)
        {
            if (cur.Name is "AbstractModel" or "CardModel" or "PowerModel" or "RelicModel" or "MonsterModel" or "PotionModel" or "OrbModel" or "EventModel" or "EnchantmentModel" or "AfflictionModel")
            {
                break;
            }
            foreach (FieldInfo field in GetDeclaredInstanceFields(cur))
            {
                if (field.IsStatic || IgnoredCustomFieldNames.Contains(field.Name))
                {
                    continue;
                }
                if (typeof(Delegate).IsAssignableFrom(field.FieldType) ||
                    typeof(System.Threading.Tasks.Task).IsAssignableFrom(field.FieldType))
                {
                    continue;
                }
                string? ns = field.FieldType.Namespace;
                if (ns != null && (ns.StartsWith("Godot", StringComparison.Ordinal) ||
                                   ns.StartsWith("MegaCrit.Sts2.Core.Nodes", StringComparison.Ordinal) ||
                                   ns.StartsWith("MegaCrit.Sts2.Core.Assets", StringComparison.Ordinal) ||
                                   ns.StartsWith("MegaCrit.Sts2.Core.Audio", StringComparison.Ordinal)))
                {
                    continue;
                }
                try
                {
                    object? val = field.GetValue(instance);
                    JsonNode? node = ConvertArbitraryValueToJson(val, maxDepth - 1);
                    string cleanName = NormalizeFieldName(field.Name);
                    if (!result.ContainsKey(cleanName))
                    {
                        result[cleanName] = node;
                    }
                }
                catch
                {
                    // Skip inaccessible field
                }
            }
            cur = cur.BaseType;
        }
        return result.Count > 0 ? result : null;
    }

    public static JsonNode? ConvertArbitraryValueToJson(object? val, int maxDepth = 2)
    {
        if (val == null)
        {
            return null;
        }
        Type t = val.GetType();
        switch (val)
        {
            case bool b:
                return JsonValue.Create(b);
            case int i:
                return JsonValue.Create(i);
            case uint u:
                return JsonValue.Create(u);
            case long l:
                return JsonValue.Create(l.ToString(CultureInfo.InvariantCulture));
            case ulong ul:
                return JsonValue.Create(ul.ToString(CultureInfo.InvariantCulture));
            case float f:
                return float.IsFinite(f) ? JsonValue.Create(f) : JsonValue.Create(f.ToString(CultureInfo.InvariantCulture));
            case double d:
                return double.IsFinite(d) ? JsonValue.Create(d) : JsonValue.Create(d.ToString(CultureInfo.InvariantCulture));
            case decimal m:
                return JsonValue.Create(m);
            case string s:
                return JsonValue.Create(s);
            case Enum e:
                return JsonValue.Create(e.ToString());
        }

        if (t.Name == "ModelId")
        {
            return JsonValue.Create(val.ToString());
        }

        if (t.Name == "Creature")
        {
            return new JsonObject
            {
                ["combat_id"] = GetUInt(val, "CombatId"),
                ["model_id"] = FormatModelId(val),
                ["side"] = GetString(val, "Side"),
                ["current_hp"] = GetInt(val, "CurrentHp"),
                ["max_hp"] = GetInt(val, "MaxHp"),
                ["block"] = GetInt(val, "Block")
            };
        }

        if (t.Name == "Player")
        {
            return new JsonObject
            {
                ["net_id"] = GetULong(val, "NetId")?.ToString(CultureInfo.InvariantCulture),
                ["character_id"] = FormatModelId(GetMember(val, "Character"))
            };
        }

        if (GetMember(val, "Id") is object modelId && modelId.GetType().Name == "ModelId")
        {
            JsonObject modelSummary = new()
            {
                ["type"] = t.Name,
                ["id"] = modelId.ToString()
            };
            if (GetInt(val, "CurrentUpgradeLevel") is int upg)
            {
                modelSummary["upgrade_level"] = upg;
            }
            if (GetInt(val, "Amount") is int amt)
            {
                modelSummary["amount"] = amt;
            }
            return modelSummary;
        }

        if (maxDepth <= 0)
        {
            return JsonValue.Create(val.ToString());
        }

        if (val is IDictionary dict)
        {
            JsonObject dictObj = new();
            foreach (DictionaryEntry entry in dict)
            {
                string key = entry.Key?.ToString() ?? "null";
                dictObj[key] = ConvertArbitraryValueToJson(entry.Value, maxDepth - 1);
            }
            return dictObj;
        }

        if (val is IEnumerable enumerable and not string)
        {
            JsonArray arr = new();
            int count = 0;
            foreach (object? item in enumerable)
            {
                if (count++ >= 128)
                {
                    arr.Add(JsonValue.Create("<truncated>"));
                    break;
                }
                arr.Add(ConvertArbitraryValueToJson(item, maxDepth - 1));
            }
            return arr;
        }

        // Plain data object / struct (such as PowerModel._internalData)
        JsonObject obj = new()
        {
            ["_type"] = t.Name
        };
        foreach (FieldInfo f in t.GetFields(AllInstanceFlags))
        {
            if (f.IsStatic || typeof(Delegate).IsAssignableFrom(f.FieldType) || typeof(System.Threading.Tasks.Task).IsAssignableFrom(f.FieldType))
            {
                continue;
            }
            try
            {
                string cleanName = NormalizeFieldName(f.Name);
                obj[cleanName] = ConvertArbitraryValueToJson(f.GetValue(val), maxDepth - 1);
            }
            catch
            {
                // Ignore
            }
        }
        return obj;
    }

    public static string NormalizeFieldName(string rawName)
    {
        if (rawName.StartsWith('<') && rawName.Contains(">k__BackingField", StringComparison.Ordinal))
        {
            int end = rawName.IndexOf('>');
            if (end > 1)
            {
                return rawName.Substring(1, end - 1);
            }
        }
        return rawName.TrimStart('_');
    }

    /// <summary>
    /// Pure 64-bit FNV-1a checksum matching Sts2Model.Replay.Timeline.fnv1aString and DiffTest/Sts2Oracle.
    /// </summary>
    public static ulong ComputeFnv1a64(string text)
    {
        const ulong offsetBasis = 14695981039346656037UL;
        const ulong prime = 1099511628211UL;
        ulong hash = offsetBasis;
        byte[] bytes = Encoding.UTF8.GetBytes(text);
        for (int i = 0; i < bytes.Length; i++)
        {
            hash = (hash ^ bytes[i]) * prime;
        }
        return hash;
    }
}
