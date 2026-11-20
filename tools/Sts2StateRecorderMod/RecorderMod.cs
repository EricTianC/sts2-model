using System;
using System.Collections;
using System.Collections.Generic;
using System.Globalization;
using System.Linq.Expressions;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text.Json.Nodes;
using HarmonyLib;
using MegaCrit.Sts2.Core.Logging;
using MegaCrit.Sts2.Core.Modding;
using static Sts2StateRecorder.ReflectionAccessor;

namespace Sts2StateRecorder;

/// <summary>
/// Main entry point for the STS2 Full State & Action Recorder Mod (Track A).
/// Loaded automatically by MegaCrit.Sts2.Core.Modding.ModManager via [ModInitializer].
/// </summary>
[ModInitializer(nameof(Initialize))]
public static class RecorderMod
{
    public const string ModId = "sts2_ideal.Sts2StateRecorder";

    private static readonly object InitLock = new();
    private static bool _isInitialized;
    private static Harmony? _harmony;
    private static RecorderSession? _session;

    // Tracks objects to which we have already attached dynamic event handlers
    private static readonly ConditionalWeakTable<object, List<Delegate>> AttachedObjectHandlers = new();
    private static bool _globalManagersBound;

    internal static RecorderSession? Session => _session;

    public static void Initialize()
    {
        lock (InitLock)
        {
            if (_isInitialized)
            {
                return;
            }
            _isInitialized = true;

            try
            {
                _session = new RecorderSession();
                Log.Info($"[Sts2StateRecorder] Initializing full state & action recorder. Output root: {_session.OutputRootDir}");

                _harmony = new Harmony(ModId);
                ApplyHarmonyPatches(_harmony);
                TryBindGlobalSingletonEvents();

                Log.Info("[Sts2StateRecorder] Initialization complete.");
            }
            catch (Exception ex)
            {
                Log.Error($"[Sts2StateRecorder] Exception during Initialize: {ex}");
            }
        }
    }

    // ========================================================================
    // Dynamic Event Subscription Engine (Zero Hard Type Coupling)
    // ========================================================================

    internal static Delegate? CreateDynamicEventHandler(Type delegateType, Action<object?[]> callback)
    {
        MethodInfo? invoke = delegateType.GetMethod("Invoke");
        if (invoke == null || invoke.ReturnType != typeof(void))
        {
            return null;
        }
        ParameterInfo[] pars = invoke.GetParameters();
        ParameterExpression[] paramExprs = new ParameterExpression[pars.Length];
        Expression[] boxedArgs = new Expression[pars.Length];
        for (int i = 0; i < pars.Length; i++)
        {
            paramExprs[i] = Expression.Parameter(pars[i].ParameterType, $"p{i}");
            boxedArgs[i] = Expression.Convert(paramExprs[i], typeof(object));
        }
        NewArrayExpression arrayExpr = Expression.NewArrayInit(typeof(object), boxedArgs);
        Expression callExpr = Expression.Invoke(Expression.Constant(callback), arrayExpr);
        return Expression.Lambda(delegateType, callExpr, paramExprs).Compile();
    }

    internal static bool SubscribeEvent(object? target, string eventName, Action<object?[]> callback)
    {
        if (target == null)
        {
            return false;
        }
        try
        {
            Type type = target.GetType();
            EventInfo? evt = type.GetEvent(eventName, BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic);
            if (evt?.EventHandlerType == null)
            {
                return false;
            }
            Delegate? handler = CreateDynamicEventHandler(evt.EventHandlerType, callback);
            if (handler == null)
            {
                return false;
            }
            evt.AddEventHandler(target, handler);
            return true;
        }
        catch (Exception ex)
        {
            Log.Warn($"[Sts2StateRecorder] Failed to subscribe event '{eventName}' on {target.GetType().Name}: {ex.Message}");
            return false;
        }
    }

    internal static bool TryMarkObjectBound(object? target)
    {
        if (target == null)
        {
            return false;
        }
        if (AttachedObjectHandlers.TryGetValue(target, out _))
        {
            return false;
        }
        AttachedObjectHandlers.Add(target, new List<Delegate>());
        return true;
    }

    // ========================================================================
    // Global & Per-Run Event Binding
    // ========================================================================

    internal static void TryBindGlobalSingletonEvents()
    {
        if (_globalManagersBound)
        {
            return;
        }

        object? runMgr = StateSnapshotExtractor.GetRunManagerInstance();
        object? combatMgr = StateSnapshotExtractor.GetCombatManagerInstance();
        if (runMgr == null || combatMgr == null)
        {
            return;
        }

        _globalManagersBound = true;

        // RunManager global events
        SubscribeEvent(runMgr, "RunStarted", args =>
        {
            object? runState = args.Length > 0 ? args[0] : StateSnapshotExtractor.GetRunState(runMgr);
            BindPerRunSynchronizers(runMgr);
            _session?.StartNewRunFile(runState);
            _session?.RecordEvent(
                eventKind: "run_started",
                includeFullState: true,
                includeCanonicalSave: true,
                drainHistoryFirst: false);
        });

        SubscribeEvent(runMgr, "ActEntered", _ =>
        {
            BindPerRunSynchronizers(runMgr);
            _session?.RecordEvent(
                eventKind: "act_entered",
                includeFullState: true,
                includeCanonicalSave: true);
        });

        SubscribeEvent(runMgr, "RoomEntered", _ =>
        {
            BindPerRunSynchronizers(runMgr);
            _session?.RecordEvent(
                eventKind: "room_entered",
                includeFullState: true,
                includeCanonicalSave: true);
        });

        SubscribeEvent(runMgr, "RoomExited", _ =>
        {
            _session?.RecordEvent(
                eventKind: "room_exited",
                includeFullState: true,
                includeCanonicalSave: true);
        });

        SubscribeEvent(runMgr, "MapChanged", args =>
        {
            JsonObject payload = new()
            {
                ["re_generated"] = args.Length > 0 && args[0] is bool b ? b : null
            };
            _session?.RecordEvent(
                eventKind: "map_changed",
                payload: payload,
                includeFullState: true,
                includeCanonicalSave: true);
        });

        // CombatManager global events
        SubscribeEvent(combatMgr, "CombatSetUp", _ =>
        {
            BindPerRunSynchronizers(runMgr);
            _session?.OnCombatStarted();
            _session?.RecordEvent(
                eventKind: "combat_setup",
                includeFullState: true,
                includeCanonicalSave: true,
                drainHistoryFirst: false);
        });

        SubscribeEvent(combatMgr, "CombatBegan", _ =>
        {
            _session?.RecordEvent(
                eventKind: "combat_began",
                includeFullState: true,
                includeCanonicalSave: false);
        });

        SubscribeEvent(combatMgr, "CombatWon", _ =>
        {
            _session?.RecordEvent(
                eventKind: "combat_won",
                includeFullState: true,
                includeCanonicalSave: false);
        });

        SubscribeEvent(combatMgr, "CombatEnded", _ =>
        {
            _session?.RecordEvent(
                eventKind: "combat_ended",
                includeFullState: true,
                includeCanonicalSave: true);
        });

        SubscribeEvent(combatMgr, "CreaturesChanged", _ =>
        {
            _session?.RecordEvent(
                eventKind: "combat_creatures_changed",
                includeFullState: true,
                includeCanonicalSave: false);
        });

        SubscribeEvent(combatMgr, "TurnStarted", _ =>
        {
            _session?.RecordEvent(
                eventKind: "turn_started",
                includeFullState: true,
                includeCanonicalSave: false);
        });

        SubscribeEvent(combatMgr, "TurnEnded", _ =>
        {
            _session?.RecordEvent(
                eventKind: "turn_ended",
                includeFullState: true,
                includeCanonicalSave: false);
        });

        SubscribeEvent(combatMgr, "AboutToSwitchToEnemyTurn", _ =>
        {
            _session?.RecordEvent(
                eventKind: "about_to_switch_to_enemy_turn",
                includeFullState: true,
                includeCanonicalSave: false);
        });

        SubscribeEvent(combatMgr, "PlayerEndedTurn", args =>
        {
            object? player = args.Length > 0 ? args[0] : null;
            bool? canUnend = args.Length > 1 && args[1] is bool b ? b : null;
            JsonObject payload = new()
            {
                ["player_net_id"] = GetULong(player, "NetId")?.ToString(CultureInfo.InvariantCulture),
                ["character_id"] = FormatModelId(GetMember(player, "Character")),
                ["can_unend"] = canUnend
            };
            _session?.RecordEvent(
                eventKind: "player_ended_turn",
                payload: payload,
                includeFullState: true);
        });

        SubscribeEvent(combatMgr, "PlayerUnendedTurn", args =>
        {
            object? player = args.Length > 0 ? args[0] : null;
            JsonObject payload = new()
            {
                ["player_net_id"] = GetULong(player, "NetId")?.ToString(CultureInfo.InvariantCulture),
                ["character_id"] = FormatModelId(GetMember(player, "Character"))
            };
            _session?.RecordEvent(
                eventKind: "player_unended_turn",
                payload: payload,
                includeFullState: true);
        });

        // CombatHistory.Changed real-time micro-event stream
        object? history = GetMember(combatMgr, "History");
        if (TryMarkObjectBound(history))
        {
            SubscribeEvent(history, "Changed", _ =>
            {
                _session?.DrainPendingCombatHistoryEntries(includeStateSnapshotOnEach: true);
            });
        }
    }

    internal static void BindPerRunSynchronizers(object? runMgr)
    {
        runMgr ??= StateSnapshotExtractor.GetRunManagerInstance();
        if (runMgr == null)
        {
            return;
        }

        // 1. ActionQueueSet
        object? actionQueueSet = GetMember(runMgr, "ActionQueueSet");
        if (TryMarkObjectBound(actionQueueSet))
        {
            SubscribeEvent(actionQueueSet, "ActionEnqueued", args =>
            {
                object? action = args.Length > 0 ? args[0] : null;
                BindIndividualGameActionEvents(action);
                JsonObject payload = new()
                {
                    ["action"] = StateSnapshotExtractor.ExtractGameAction(action)
                };
                _session?.RecordEvent(
                    eventKind: "action_enqueued",
                    payload: payload,
                    includeFullState: true);
            });

            SubscribeEvent(actionQueueSet, "ActionResumed", args =>
            {
                uint? actionId = args.Length > 0 && args[0] is uint u ? u : null;
                JsonObject payload = new()
                {
                    ["resumed_action_id"] = actionId
                };
                _session?.RecordEvent(
                    eventKind: "action_resumed_in_queue",
                    payload: payload,
                    includeFullState: true);
            });
        }

        // 2. ActionExecutor
        object? actionExecutor = GetMember(runMgr, "ActionExecutor");
        if (TryMarkObjectBound(actionExecutor))
        {
            SubscribeEvent(actionExecutor, "BeforeActionExecuted", args =>
            {
                object? action = args.Length > 0 ? args[0] : null;
                BindIndividualGameActionEvents(action);
                _session?.SetActiveAction(action);
                JsonObject payload = new()
                {
                    ["action"] = StateSnapshotExtractor.ExtractGameAction(action)
                };
                _session?.RecordEvent(
                    eventKind: "action_before_execute",
                    payload: payload,
                    includeFullState: true);
            });

            SubscribeEvent(actionExecutor, "JustBeforeActionFinishedExecuting", args =>
            {
                object? action = args.Length > 0 ? args[0] : null;
                JsonObject payload = new()
                {
                    ["action"] = StateSnapshotExtractor.ExtractGameAction(action)
                };
                _session?.RecordEvent(
                    eventKind: "action_just_before_finished",
                    payload: payload,
                    includeFullState: true);
            });

            SubscribeEvent(actionExecutor, "AfterActionExecuted", args =>
            {
                object? action = args.Length > 0 ? args[0] : null;
                JsonObject payload = new()
                {
                    ["action"] = StateSnapshotExtractor.ExtractGameAction(action)
                };
                _session?.RecordEvent(
                    eventKind: "action_after_execute",
                    payload: payload,
                    includeFullState: true);
                _session?.SetActiveAction(null);
            });
        }

        // 3. PlayerChoiceSynchronizer
        object? choiceSync = GetMember(runMgr, "PlayerChoiceSynchronizer");
        if (TryMarkObjectBound(choiceSync))
        {
            SubscribeEvent(choiceSync, "PlayerChoiceReceived", args =>
            {
                object? player = args.Length > 0 ? args[0] : null;
                uint choiceId = args.Length > 1 && args[1] is uint u ? u : 0u;
                object? netResult = args.Length > 2 ? args[2] : null;

                JsonObject payload = StateSnapshotExtractor.ExtractPlayerChoiceResult(player, choiceId, netResult);
                _session?.RecordEvent(
                    eventKind: "player_choice_received",
                    payload: payload,
                    includeFullState: true);
            });
        }

        // 4. ChecksumTracker
        object? checksumTracker = GetMember(runMgr, "ChecksumTracker");
        if (TryMarkObjectBound(checksumTracker))
        {
            SubscribeEvent(checksumTracker, "ChecksumGenerated", args =>
            {
                object? netChecksumData = args.Length > 0 ? args[0] : null;
                string? context = args.Length > 1 ? args[1] as string : null;
                object? fullCombatState = args.Length > 2 ? args[2] : null;

                JsonObject payload = new()
                {
                    ["checksum_id"] = GetUInt(netChecksumData, "id"),
                    ["engine_checksum_u32"] = GetUInt(netChecksumData, "checksum"),
                    ["context"] = context,
                    ["net_full_combat_state"] = StateSnapshotExtractor.ExtractNetFullCombatState(fullCombatState)
                };
                _session?.RecordEvent(
                    eventKind: "checksum_generated",
                    payload: payload,
                    includeFullState: true);
            });

            SubscribeEvent(checksumTracker, "StateDiverged", args =>
            {
                ulong? remoteId = args.Length > 0 && args[0] is ulong ul ? ul : null;
                object? remoteState = args.Length > 1 ? args[1] : null;
                JsonObject payload = new()
                {
                    ["diverged_from_player_id"] = remoteId?.ToString(CultureInfo.InvariantCulture),
                    ["remote_net_full_combat_state"] = StateSnapshotExtractor.ExtractNetFullCombatState(remoteState)
                };
                _session?.RecordEvent(
                    eventKind: "state_diverged",
                    payload: payload,
                    includeFullState: true);
            });
        }

        // 5. MapSelectionSynchronizer
        object? mapSync = GetMember(runMgr, "MapSelectionSynchronizer");
        if (TryMarkObjectBound(mapSync))
        {
            SubscribeEvent(mapSync, "PlayerVoteChanged", args =>
            {
                object? player = args.Length > 0 ? args[0] : null;
                object? oldVote = args.Length > 1 ? args[1] : null;
                object? newVote = args.Length > 2 ? args[2] : null;
                JsonObject payload = new()
                {
                    ["player_net_id"] = GetULong(player, "NetId")?.ToString(CultureInfo.InvariantCulture),
                    ["old_vote"] = ConvertArbitraryValueToJson(oldVote, 2),
                    ["new_vote"] = ConvertArbitraryValueToJson(newVote, 2)
                };
                _session?.RecordEvent(
                    eventKind: "map_vote_changed",
                    payload: payload,
                    includeFullState: true);
            });
        }

        // 6. RestSiteSynchronizer
        object? restSync = GetMember(runMgr, "RestSiteSynchronizer");
        if (TryMarkObjectBound(restSync))
        {
            SubscribeEvent(restSync, "BeforePlayerOptionChosen", args =>
            {
                object? option = args.Length > 0 ? args[0] : null;
                ulong? playerId = args.Length > 1 && args[1] is ulong ul ? ul : null;
                JsonObject payload = new()
                {
                    ["player_net_id"] = playerId?.ToString(CultureInfo.InvariantCulture),
                    ["option_class"] = option?.GetType().Name,
                    ["option_id"] = GetString(option, "OptionId"),
                    ["option_summary"] = option?.ToString()
                };
                _session?.RecordEvent(
                    eventKind: "rest_site_option_before",
                    payload: payload,
                    includeFullState: true);
            });

            SubscribeEvent(restSync, "AfterPlayerOptionChosen", args =>
            {
                object? option = args.Length > 0 ? args[0] : null;
                bool? success = args.Length > 1 && args[1] is bool b ? b : null;
                ulong? playerId = args.Length > 2 && args[2] is ulong ul ? ul : null;
                JsonObject payload = new()
                {
                    ["player_net_id"] = playerId?.ToString(CultureInfo.InvariantCulture),
                    ["option_class"] = option?.GetType().Name,
                    ["option_id"] = GetString(option, "OptionId"),
                    ["success"] = success,
                    ["option_summary"] = option?.ToString()
                };
                _session?.RecordEvent(
                    eventKind: "rest_site_option_after",
                    payload: payload,
                    includeFullState: true,
                    includeCanonicalSave: true);
            });
        }

        // 7. EventSynchronizer
        object? eventSync = GetMember(runMgr, "EventSynchronizer");
        if (TryMarkObjectBound(eventSync))
        {
            SubscribeEvent(eventSync, "PlayerVoteChanged", args =>
            {
                object? player = args.Length > 0 ? args[0] : null;
                JsonObject payload = new()
                {
                    ["player_net_id"] = GetULong(player, "NetId")?.ToString(CultureInfo.InvariantCulture)
                };
                _session?.RecordEvent(
                    eventKind: "event_vote_changed",
                    payload: payload,
                    includeFullState: true);
            });
        }

        // 8. RewardsSetSynchronizer
        object? rewardsSetSync = GetMember(runMgr, "RewardsSetSynchronizer");
        if (TryMarkObjectBound(rewardsSetSync))
        {
            SubscribeEvent(rewardsSetSync, "RewardsSkippedDuringRoomExit", _ =>
            {
                _session?.RecordEvent(
                    eventKind: "rewards_skipped_during_room_exit",
                    includeFullState: true,
                    includeCanonicalSave: true);
            });
        }
    }

    private static void BindIndividualGameActionEvents(object? action)
    {
        if (!TryMarkObjectBound(action))
        {
            return;
        }

        SubscribeEvent(action, "BeforePausedForPlayerChoice", args =>
        {
            object? act = args.Length > 0 ? args[0] : action;
            JsonObject payload = new()
            {
                ["action"] = StateSnapshotExtractor.ExtractGameAction(act)
            };
            _session?.RecordEvent(
                eventKind: "action_paused_for_player_choice",
                payload: payload,
                includeFullState: true);
        });

        SubscribeEvent(action, "BeforeReadyToResumeAfterPlayerChoice", args =>
        {
            object? act = args.Length > 0 ? args[0] : action;
            JsonObject payload = new()
            {
                ["action"] = StateSnapshotExtractor.ExtractGameAction(act)
            };
            _session?.RecordEvent(
                eventKind: "action_ready_to_resume_after_choice",
                payload: payload,
                includeFullState: true);
        });

        SubscribeEvent(action, "BeforeResumedAfterPlayerChoice", args =>
        {
            object? act = args.Length > 0 ? args[0] : action;
            _session?.SetActiveAction(act);
            JsonObject payload = new()
            {
                ["action"] = StateSnapshotExtractor.ExtractGameAction(act)
            };
            _session?.RecordEvent(
                eventKind: "action_resumed_after_choice",
                payload: payload,
                includeFullState: true);
        });

        SubscribeEvent(action, "BeforeCancelled", args =>
        {
            object? act = args.Length > 0 ? args[0] : action;
            JsonObject payload = new()
            {
                ["action"] = StateSnapshotExtractor.ExtractGameAction(act)
            };
            _session?.RecordEvent(
                eventKind: "action_cancelled",
                payload: payload,
                includeFullState: true);
        });
    }

    // ========================================================================
    // Non-Intrusive Harmony Postfix Patches (Lifecycle + Out-of-Combat Actions)
    // ========================================================================

    private static void ApplyHarmonyPatches(Harmony harmony)
    {
        TryPatchPostfix(harmony, "MegaCrit.Sts2.Core.Runs.RunManager", "InitializeShared", nameof(Postfix_RunManager_InitializeShared));
        TryPatchPostfix(harmony, "MegaCrit.Sts2.Core.Runs.RunManager", "InitializeRunLobby", nameof(Postfix_RunManager_InitializeRunLobby));
        TryPatchPostfix(harmony, "MegaCrit.Sts2.Core.Runs.RunManager", "InitializeNewRun", nameof(Postfix_RunManager_InitializeNewRun));
        TryPatchPostfix(harmony, "MegaCrit.Sts2.Core.Runs.RunManager", "InitializeSavedRun", nameof(Postfix_RunManager_InitializeSavedRun));
        TryPatchPostfix(harmony, "MegaCrit.Sts2.Core.Runs.RunManager", "CleanUp", nameof(Postfix_RunManager_CleanUp));

        TryPatchPostfix(harmony, "MegaCrit.Sts2.Core.Multiplayer.Game.EventSynchronizer", "BeginEvent", nameof(Postfix_EventSynchronizer_BeginEvent));
        TryPatchPostfix(harmony, "MegaCrit.Sts2.Core.Multiplayer.Game.EventSynchronizer", "ChooseOptionForEvent", nameof(Postfix_EventSynchronizer_ChooseOptionForEvent));

        TryPatchPostfix(harmony, "MegaCrit.Sts2.Core.Multiplayer.Game.MerchantSynchronizer", "OnMerchantEntered", nameof(Postfix_MerchantSynchronizer_OnMerchantEntered));
        TryPatchPostfix(harmony, "MegaCrit.Sts2.Core.Multiplayer.Game.MerchantSynchronizer", "PurchaseEntry", nameof(Postfix_MerchantSynchronizer_PurchaseEntry));
        TryPatchPostfix(harmony, "MegaCrit.Sts2.Core.Multiplayer.Game.MerchantSynchronizer", "OnMerchantExited", nameof(Postfix_MerchantSynchronizer_OnMerchantExited));

        TryPatchPostfix(harmony, "MegaCrit.Sts2.Core.Multiplayer.Game.RestSiteSynchronizer", "BeginRestSite", nameof(Postfix_RestSiteSynchronizer_BeginRestSite));

        TryPatchPostfix(harmony, "MegaCrit.Sts2.Core.Multiplayer.Game.RewardsSetSynchronizer", "BeginRewardsSet", nameof(Postfix_RewardsSetSynchronizer_BeginRewardsSet));
        TryPatchPostfix(harmony, "MegaCrit.Sts2.Core.Multiplayer.Game.RewardsSetSynchronizer", "SelectRewardForPlayer", nameof(Postfix_RewardsSetSynchronizer_SelectRewardForPlayer));
        TryPatchPostfix(harmony, "MegaCrit.Sts2.Core.Multiplayer.Game.RewardsSetSynchronizer", "SkipRewardsSetOnStackTopForPlayer", nameof(Postfix_RewardsSetSynchronizer_SkipRewardsSet));

        TryPatchPostfix(harmony, "MegaCrit.Sts2.Core.Commands.CardSelectCmd", "LogChoice", nameof(Postfix_CardSelectCmd_LogChoice));
    }

    private static void TryPatchPostfix(Harmony harmony, string targetTypeFullName, string methodName, string postfixMethodName)
    {
        try
        {
            Type? targetType = FindType(targetTypeFullName);
            if (targetType == null)
            {
                return;
            }
            MethodInfo? postfixInfo = typeof(RecorderMod).GetMethod(
                postfixMethodName,
                BindingFlags.Static | BindingFlags.NonPublic | BindingFlags.Public);
            if (postfixInfo == null)
            {
                return;
            }

            int patchedCount = 0;
            foreach (MethodInfo method in targetType.GetMethods(
                         BindingFlags.Instance | BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly))
            {
                if (method.Name == methodName && !method.IsAbstract && !method.IsGenericMethodDefinition)
                {
                    try
                    {
                        harmony.Patch(method, postfix: new HarmonyMethod(postfixInfo));
                        patchedCount++;
                    }
                    catch (Exception innerEx)
                    {
                        Log.Warn($"[Sts2StateRecorder] Skipping overload {targetType.Name}.{method}: {innerEx.Message}");
                    }
                }
            }
            if (patchedCount > 0)
            {
                Log.Debug($"[Sts2StateRecorder] Patched {targetType.Name}.{methodName} ({patchedCount} overload(s))");
            }
        }
        catch (Exception ex)
        {
            Log.Warn($"[Sts2StateRecorder] Could not patch {targetTypeFullName}.{methodName}: {ex.Message}");
        }
    }

    private static void Postfix_RunManager_InitializeShared(object? __instance)
    {
        TryBindGlobalSingletonEvents();
        BindPerRunSynchronizers(__instance);
    }

    private static void Postfix_RunManager_InitializeRunLobby(object? __instance)
    {
        BindPerRunSynchronizers(__instance);
    }

    private static void Postfix_RunManager_InitializeNewRun(object? __instance)
    {
        TryBindGlobalSingletonEvents();
        BindPerRunSynchronizers(__instance);
        object? runState = StateSnapshotExtractor.GetRunState(__instance);
        _session?.StartNewRunFile(runState);
        _session?.RecordEvent(
            eventKind: "run_initialized_new",
            includeFullState: true,
            includeCanonicalSave: true,
            drainHistoryFirst: false);
    }

    private static void Postfix_RunManager_InitializeSavedRun(object? __instance)
    {
        TryBindGlobalSingletonEvents();
        BindPerRunSynchronizers(__instance);
        object? runState = StateSnapshotExtractor.GetRunState(__instance);
        _session?.StartNewRunFile(runState);
        _session?.RecordEvent(
            eventKind: "run_initialized_from_save",
            includeFullState: true,
            includeCanonicalSave: true,
            drainHistoryFirst: false);
    }

    private static void Postfix_RunManager_CleanUp()
    {
        _session?.RecordEvent(
            eventKind: "run_cleanup",
            includeFullState: true,
            includeCanonicalSave: false);
    }

    private static void Postfix_EventSynchronizer_BeginEvent(object? __instance)
    {
        object? canonicalEvent = GetMember(__instance, "_canonicalEvent");
        JsonObject payload = new()
        {
            ["event_id"] = FormatModelId(canonicalEvent),
            ["is_shared"] = GetBool(canonicalEvent, "IsShared")
        };

        JsonArray playerEventsArr = new();
        if (GetMember(__instance, "Events") is IEnumerable events)
        {
            foreach (object? ev in events)
            {
                if (ev != null)
                {
                    JsonArray optsArr = new();
                    if (GetMember(ev, "CurrentOptions") is IEnumerable opts)
                    {
                        int optIdx = 0;
                        foreach (object? opt in opts)
                        {
                            if (opt != null)
                            {
                                optsArr.Add(new JsonObject
                                {
                                    ["index"] = optIdx++,
                                    ["text_key"] = GetString(opt, "TextKey"),
                                    ["is_locked"] = GetBool(opt, "IsLocked"),
                                    ["was_chosen"] = GetBool(opt, "WasChosen")
                                });
                            }
                        }
                    }
                    playerEventsArr.Add(new JsonObject
                    {
                        ["owner_net_id"] = GetULong(GetMember(ev, "Owner"), "NetId")?.ToString(CultureInfo.InvariantCulture),
                        ["event_id"] = FormatModelId(ev),
                        ["is_finished"] = GetBool(ev, "IsFinished"),
                        ["options"] = optsArr
                    });
                }
            }
        }
        payload["player_events"] = playerEventsArr;

        _session?.RecordEvent(
            eventKind: "event_began",
            payload: payload,
            includeFullState: true,
            includeCanonicalSave: false);
    }

    private static void Postfix_EventSynchronizer_ChooseOptionForEvent(object? __instance, int optionIndex)
    {
        object? canonicalEvent = GetMember(__instance, "_canonicalEvent");
        JsonObject payload = new()
        {
            ["event_id"] = FormatModelId(canonicalEvent),
            ["chosen_option_index"] = optionIndex,
            ["page_index"] = GetUInt(__instance, "_pageIndex")
        };
        _session?.RecordEvent(
            eventKind: "event_option_chosen",
            payload: payload,
            includeFullState: true,
            includeCanonicalSave: true);
    }

    private static void Postfix_MerchantSynchronizer_OnMerchantEntered(object? __instance)
    {
        JsonObject payload = new()
        {
            ["inventories"] = ConvertArbitraryValueToJson(GetMember(__instance, "_inventories"), 3)
        };
        _session?.RecordEvent(
            eventKind: "merchant_entered",
            payload: payload,
            includeFullState: true,
            includeCanonicalSave: false);
    }

    private static void Postfix_MerchantSynchronizer_PurchaseEntry(uint entryId)
    {
        JsonObject payload = new()
        {
            ["purchased_entry_id"] = entryId
        };
        _session?.RecordEvent(
            eventKind: "merchant_entry_purchased",
            payload: payload,
            includeFullState: true,
            includeCanonicalSave: true);
    }

    private static void Postfix_MerchantSynchronizer_OnMerchantExited()
    {
        _session?.RecordEvent(
            eventKind: "merchant_exited",
            includeFullState: true,
            includeCanonicalSave: true);
    }

    private static void Postfix_RestSiteSynchronizer_BeginRestSite(object? __instance)
    {
        JsonObject payload = new()
        {
            ["rest_sites"] = ConvertArbitraryValueToJson(GetMember(__instance, "_restSites"), 3)
        };
        _session?.RecordEvent(
            eventKind: "rest_site_began",
            payload: payload,
            includeFullState: true);
    }

    private static void Postfix_RewardsSetSynchronizer_BeginRewardsSet(object? __instance)
    {
        JsonObject payload = new()
        {
            ["reward_states"] = ConvertArbitraryValueToJson(GetMember(__instance, "_rewardStates"), 3)
        };
        _session?.RecordEvent(
            eventKind: "rewards_set_began",
            payload: payload,
            includeFullState: true);
    }

    private static void Postfix_RewardsSetSynchronizer_SelectRewardForPlayer(object? __instance)
    {
        JsonObject payload = new()
        {
            ["reward_states"] = ConvertArbitraryValueToJson(GetMember(__instance, "_rewardStates"), 3)
        };
        _session?.RecordEvent(
            eventKind: "reward_selected",
            payload: payload,
            includeFullState: true,
            includeCanonicalSave: true);
    }

    private static void Postfix_RewardsSetSynchronizer_SkipRewardsSet()
    {
        _session?.RecordEvent(
            eventKind: "rewards_set_skipped",
            includeFullState: true,
            includeCanonicalSave: true);
    }

    private static void Postfix_CardSelectCmd_LogChoice(IEnumerable? cards)
    {
        JsonArray chosenArr = new();
        if (cards != null)
        {
            int idx = 0;
            foreach (object? card in cards)
            {
                if (card != null)
                {
                    chosenArr.Add(StateSnapshotExtractor.ExtractCardState(card, idx++, inCombat: true));
                }
            }
        }
        JsonObject payload = new()
        {
            ["chosen_cards"] = chosenArr
        };
        _session?.RecordEvent(
            eventKind: "card_select_cmd_choice",
            payload: payload,
            includeFullState: true);
    }
}
