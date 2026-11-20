using System;
using System.Collections;
using System.Collections.Generic;
using System.Globalization;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using static Sts2StateRecorder.ReflectionAccessor;

namespace Sts2StateRecorder;

/// <summary>
/// Lossless deep state and action extractor for Slay the Spire 2 (Track A).
/// Captures all RunState, CombatState, Creature, MonsterMoveStateMachine, Player,
/// 5 CombatPiles, CardModel, PowerModel (_internalData), RelicModel, PotionModel,
/// OrbQueue, ArrowSlot, Rng (Xoshiro256** s0..s3 + counter), Odds (with IEEE-754 f32_bits),
/// ActionQueueSet, GameAction, PlayerChoiceResult, and all 18 CombatHistoryEntry types.
/// </summary>
internal static class StateSnapshotExtractor
{
    public static object? GetRunManagerInstance()
        => GetStaticMember("MegaCrit.Sts2.Core.Runs.RunManager", "Instance");

    public static object? GetCombatManagerInstance()
        => GetStaticMember("MegaCrit.Sts2.Core.Combat.CombatManager", "Instance");

    public static object? GetRunState(object? runManager = null)
    {
        runManager ??= GetRunManagerInstance();
        return GetMember(runManager, "State");
    }

    public static object? GetCombatState(object? runState = null)
    {
        object? combatMgr = GetCombatManagerInstance();
        object? turnState = GetMember(combatMgr, "_turnState");
        object? st = GetMember(turnState, "State");
        if (st != null)
        {
            return st;
        }
        runState ??= GetRunState();
        if (GetMember(runState, "Players") is IEnumerable players)
        {
            foreach (object? player in players)
            {
                object? creature = GetMember(player, "Creature");
                object? cs = GetMember(creature, "CombatState");
                if (cs != null && cs.GetType().Name != "NullCombatState")
                {
                    return cs;
                }
            }
        }
        return null;
    }

    /// <summary>
    /// Captures the complete state snapshot at the current instant (Combat + Run + ActionQueues + FNV-1a Checksum).
    /// </summary>
    public static JsonObject ExtractFullSnapshot(bool includeCanonicalSaveJson = false)
    {
        object? runMgr = GetRunManagerInstance();
        object? runState = GetRunState(runMgr);
        object? combatMgr = GetCombatManagerInstance();
        object? combatState = GetCombatState(runState);

        JsonObject snapshot = new()
        {
            ["is_run_in_progress"] = GetBool(runMgr, "IsInProgress") ?? (runState != null),
            ["is_combat_in_progress"] = GetBool(combatMgr, "IsInProgress") ?? false,
            ["is_combat_starting"] = GetBool(combatMgr, "IsStarting") ?? false,
            ["is_combat_ending"] = GetBool(combatMgr, "IsEnding") ?? false
        };

        if (runState != null)
        {
            snapshot["run_state"] = ExtractRunState(runMgr, runState, includeCanonicalSaveJson);
        }

        if (combatState != null)
        {
            JsonObject combatJson = ExtractCombatState(combatMgr, combatState);
            snapshot["combat_state"] = combatJson;
        }

        if (runMgr != null)
        {
            snapshot["action_queues"] = ExtractActionQueues(runMgr);
            snapshot["synchronizer_ids"] = ExtractSynchronizerIds(runMgr);
        }

        string canonicalDigestSource = BuildCanonicalStateDigestString(snapshot);
        ulong fnv1a = ComputeFnv1a64(canonicalDigestSource);
        snapshot["fnv1a_checksum_u64"] = fnv1a.ToString(CultureInfo.InvariantCulture);
        snapshot["fnv1a_checksum_hex"] = fnv1a.ToString("x16", CultureInfo.InvariantCulture);

        return snapshot;
    }

    public static JsonObject ExtractRunState(object? runMgr, object runState, bool includeCanonicalSaveJson)
    {
        JsonObject obj = new()
        {
            ["current_act_index"] = GetInt(runState, "CurrentActIndex"),
            ["act_id"] = FormatModelId(GetMember(runState, "Act")),
            ["act_floor"] = GetInt(runState, "ActFloor"),
            ["total_floor"] = GetInt(runState, "TotalFloor"),
            ["ascension_level"] = GetInt(runState, "AscensionLevel"),
            ["game_mode"] = GetString(runState, "GameMode"),
            ["is_custom_game"] = GetBool(runState, "IsCustomGame"),
            ["next_room_id"] = GetInt(runState, "NextRoomId"),
            ["current_map_coord"] = ExtractMapCoord(GetMember(runState, "CurrentMapCoord")),
            ["current_map_point_type"] = GetString(GetMember(runState, "CurrentMapPoint"), "PointType"),
            ["visited_map_coords"] = ExtractMapCoordList(GetMember(runState, "VisitedMapCoords")),
            ["room_stack"] = ExtractRoomStack(GetMember(runState, "_currentRooms")),
            ["run_rng_set"] = ExtractRunRngSet(GetMember(runState, "Rng")),
            ["run_odds_set"] = ExtractRunOddsSet(GetMember(runState, "Odds")),
            ["shared_relic_grab_bag"] = ExtractRelicGrabBag(GetMember(runState, "SharedRelicGrabBag")),
            ["extra_fields"] = ConvertArbitraryValueToJson(GetMember(runState, "ExtraFields"), 2)
        };

        JsonArray playersArr = new();
        if (GetMember(runState, "Players") is IEnumerable players)
        {
            int slotIdx = 0;
            foreach (object? player in players)
            {
                if (player != null)
                {
                    playersArr.Add(ExtractPlayerRunState(player, slotIdx++));
                }
            }
        }
        obj["players"] = playersArr;

        if (includeCanonicalSaveJson && runMgr != null)
        {
            JsonNode? saveNode = TryExtractCanonicalSerializableRun(runMgr);
            if (saveNode != null)
            {
                obj["canonical_serializable_run"] = saveNode;
            }
        }

        return obj;
    }

    public static JsonNode? TryExtractCanonicalSerializableRun(object? runMgr)
    {
        runMgr ??= GetRunManagerInstance();
        if (runMgr == null)
        {
            return null;
        }
        try
        {
            object? serializableRun = InvokeMethod(runMgr, "ToSave", new object?[] { null });
            if (serializableRun == null)
            {
                return null;
            }
            Type? jsonUtilType = FindType("MegaCrit.Sts2.Core.Saves.JsonSerializationUtility");
            if (jsonUtilType != null)
            {
                foreach (var method in jsonUtilType.GetMethods())
                {
                    if (method.Name == "ToJson" && method.IsGenericMethodDefinition && method.GetParameters().Length == 1)
                    {
                        var closed = method.MakeGenericMethod(serializableRun.GetType());
                        if (closed.Invoke(null, new[] { serializableRun }) is string jsonStr && !string.IsNullOrWhiteSpace(jsonStr))
                        {
                            return JsonNode.Parse(jsonStr);
                        }
                    }
                }
            }
        }
        catch
        {
            // Fallback if SaveManager schema version isn't ready during early setup
        }
        return null;
    }

    public static JsonObject ExtractPlayerRunState(object player, int slotIndex)
    {
        object? creature = GetMember(player, "Creature");
        JsonObject obj = new()
        {
            ["slot_index"] = slotIndex,
            ["net_id"] = GetULong(player, "NetId")?.ToString(CultureInfo.InvariantCulture),
            ["character_id"] = FormatModelId(GetMember(player, "Character")),
            ["current_hp"] = GetInt(creature, "CurrentHp") ?? GetInt(player, "CurrentHp"),
            ["max_hp"] = GetInt(creature, "MaxHp") ?? GetInt(player, "MaxHp"),
            ["gold"] = GetInt(player, "Gold"),
            ["max_energy"] = GetInt(player, "MaxEnergy"),
            ["max_potion_count"] = GetInt(player, "MaxPotionCount"),
            ["base_orb_slot_count"] = GetInt(player, "BaseOrbSlotCount"),
            ["is_active_for_hooks"] = GetBool(player, "IsActiveForHooks"),
            ["player_rng_set"] = ExtractPlayerRngSet(GetMember(player, "PlayerRng")),
            ["player_odds_set"] = ExtractPlayerOddsSet(GetMember(player, "PlayerOdds")),
            ["relic_grab_bag"] = ExtractRelicGrabBag(GetMember(player, "RelicGrabBag")),
            ["extra_fields"] = ConvertArbitraryValueToJson(GetMember(player, "ExtraFields"), 2)
        };

        // Master Deck
        JsonArray deckArr = new();
        object? deckPile = GetMember(player, "Deck");
        if (GetMember(deckPile, "Cards") is IEnumerable deckCards)
        {
            int idx = 0;
            foreach (object? card in deckCards)
            {
                if (card != null)
                {
                    deckArr.Add(ExtractCardState(card, idx++, inCombat: false));
                }
            }
        }
        obj["master_deck"] = deckArr;

        // Relics
        JsonArray relicsArr = new();
        if (GetMember(player, "Relics") is IEnumerable relics)
        {
            int idx = 0;
            foreach (object? relic in relics)
            {
                if (relic != null)
                {
                    relicsArr.Add(ExtractRelicState(relic, idx++));
                }
            }
        }
        obj["relics"] = relicsArr;

        // Potion Slots (preserving null empty slots)
        JsonArray potionsArr = new();
        if (GetMember(player, "PotionSlots") is IEnumerable potionSlots)
        {
            int idx = 0;
            foreach (object? potion in potionSlots)
            {
                potionsArr.Add(ExtractPotionSlotState(potion, idx++));
            }
        }
        obj["potion_slots"] = potionsArr;

        return obj;
    }

    public static JsonObject ExtractCombatState(object? combatMgr, object combatState)
    {
        object? encounter = GetMember(combatState, "Encounter");
        object? turnState = GetMember(combatMgr, "_turnState");
        object? combatIdObj = GetMember(combatMgr, "CurrentCombatId") ?? GetMember(turnState, "Id");

        JsonObject obj = new()
        {
            ["combat_id"] = combatIdObj?.ToString(),
            ["round_number"] = GetInt(combatState, "RoundNumber"),
            ["current_side"] = GetString(combatState, "CurrentSide"),
            ["encounter_id"] = FormatModelId(encounter),
            ["next_creature_id"] = GetUInt(combatState, "_nextCreatureId"),
            ["is_in_progress"] = GetBool(combatMgr, "IsInProgress"),
            ["is_starting"] = GetBool(combatMgr, "IsStarting"),
            ["is_ending"] = GetBool(combatMgr, "IsEnding"),
            ["is_about_to_lose"] = GetBool(combatMgr, "IsAboutToLose"),
            ["is_enemy_turn_started"] = GetBool(combatMgr, "IsEnemyTurnStarted"),
            ["ending_player_turn_phase_one"] = GetBool(combatMgr, "EndingPlayerTurnPhaseOne"),
            ["ending_player_turn_phase_two"] = GetBool(combatMgr, "EndingPlayerTurnPhaseTwo"),
            ["player_actions_disabled"] = GetBool(combatMgr, "PlayerActionsDisabled"),
            ["dominion_id"] = FormatModelId(GetMember(combatState, "Dominion"))
        };

        // Players taking extra turn
        JsonArray extraTurnPlayers = new();
        if (GetMember(combatMgr, "PlayersTakingExtraTurn") is IEnumerable extraPlayers)
        {
            foreach (object? p in extraPlayers)
            {
                if (GetULong(p, "NetId") is ulong pid)
                {
                    extraTurnPlayers.Add(JsonValue.Create(pid.ToString(CultureInfo.InvariantCulture)));
                }
            }
        }
        obj["players_taking_extra_turn"] = extraTurnPlayers;

        // Escaped creatures
        JsonArray escapedArr = new();
        if (GetMember(combatState, "EscapedCreatures") is IEnumerable escaped)
        {
            foreach (object? c in escaped)
            {
                if (c != null)
                {
                    escapedArr.Add( new JsonObject
                    {
                        ["combat_id"] = GetUInt(c, "CombatId"),
                        ["model_id"] = FormatModelId(c)
                    });
                }
            }
        }
        obj["escaped_creatures"] = escapedArr;

        // All Creatures in combat
        JsonArray creaturesArr = new();
        if (GetMember(combatState, "Creatures") is IEnumerable creatures)
        {
            int idx = 0;
            foreach (object? creature in creatures)
            {
                if (creature != null)
                {
                    creaturesArr.Add(ExtractCreatureState(creature, idx++));
                }
            }
        }
        obj["creatures"] = creaturesArr;

        // Per-Player Combat State (5 piles, orbs, arrows, energy, stars, phase, turnNumber, pets)
        JsonArray playersCombatArr = new();
        if (GetMember(combatState, "Players") is IEnumerable combatPlayers)
        {
            int slotIdx = 0;
            foreach (object? player in combatPlayers)
            {
                if (player != null)
                {
                    playersCombatArr.Add(ExtractPlayerCombatState(player, slotIdx++));
                }
            }
        }
        obj["players"] = playersCombatArr;

        return obj;
    }

    public static JsonObject ExtractCreatureState(object creature, int index)
    {
        object? monster = GetMember(creature, "Monster");
        object? player = GetMember(creature, "Player");
        object? petOwner = GetMember(creature, "PetOwner");

        JsonObject obj = new()
        {
            ["index"] = index,
            ["combat_id"] = GetUInt(creature, "CombatId"),
            ["model_id"] = FormatModelId(creature),
            ["side"] = GetString(creature, "Side"),
            ["slot_name"] = GetString(creature, "SlotName"),
            ["is_player"] = GetBool(creature, "IsPlayer"),
            ["is_monster"] = GetBool(creature, "IsMonster"),
            ["is_pet"] = GetBool(creature, "IsPet"),
            ["pet_owner_net_id"] = GetULong(petOwner, "NetId")?.ToString(CultureInfo.InvariantCulture),
            ["player_net_id"] = GetULong(player, "NetId")?.ToString(CultureInfo.InvariantCulture),
            ["is_alive"] = GetBool(creature, "IsAlive"),
            ["is_hittable"] = GetBool(creature, "IsHittable"),
            ["is_primary_enemy"] = GetBool(creature, "IsPrimaryEnemy"),
            ["is_secondary_enemy"] = GetBool(creature, "IsSecondaryEnemy"),
            ["current_hp"] = GetInt(creature, "CurrentHp"),
            ["max_hp"] = GetInt(creature, "MaxHp"),
            ["monster_max_hp_before_modification"] = GetInt(creature, "MonsterMaxHpBeforeModification"),
            ["block"] = GetInt(creature, "Block"),
            ["hp_display"] = GetString(creature, "HpDisplay")
        };

        // Powers
        JsonArray powersArr = new();
        if (GetMember(creature, "Powers") is IEnumerable powers)
        {
            int pIdx = 0;
            foreach (object? power in powers)
            {
                if (power != null)
                {
                    powersArr.Add(ExtractPowerState(power, pIdx++));
                }
            }
        }
        obj["powers"] = powersArr;

        // Monster-specific AI & State Machine details
        if (monster != null)
        {
            obj["monster"] = ExtractMonsterDetails(monster);
        }

        return obj;
    }

    public static JsonObject ExtractPowerState(object power, int index)
    {
        object? owner = GetMember(power, "Owner");
        object? applier = GetMember(power, "Applier");
        object? target = GetMember(power, "Target");
        object? internalData = GetMember(power, "_internalData");

        JsonObject obj = new()
        {
            ["index"] = index,
            ["id"] = FormatModelId(power),
            ["entry"] = FormatModelEntry(power),
            ["amount"] = GetInt(power, "Amount"),
            ["amount_on_turn_start"] = GetInt(power, "AmountOnTurnStart"),
            ["display_amount"] = GetInt(power, "DisplayAmount"),
            ["type"] = GetString(power, "Type"),
            ["type_for_current_amount"] = GetString(power, "TypeForCurrentAmount"),
            ["stack_type"] = GetString(power, "StackType"),
            ["instance_type"] = GetString(power, "InstanceType"),
            ["allow_negative"] = GetBool(power, "AllowNegative"),
            ["skip_next_duration_tick"] = GetBool(power, "SkipNextDurationTick"),
            ["is_visible"] = GetBool(power, "IsVisible"),
            ["owner_combat_id"] = GetUInt(owner, "CombatId"),
            ["applier_combat_id"] = GetUInt(applier, "CombatId"),
            ["target_combat_id"] = GetUInt(target, "CombatId"),
            ["dynamic_vars"] = ExtractDynamicVarSet(GetMember(power, "_dynamicVars"))
        };

        if (internalData != null)
        {
            obj["internal_data"] = ConvertArbitraryValueToJson(internalData, 3);
        }

        JsonObject? customFields = InspectCustomDeclaredFields(power, stopAtBaseType: null, maxDepth: 2);
        if (customFields != null)
        {
            obj["custom_fields"] = customFields;
        }

        return obj;
    }

    public static JsonObject ExtractMonsterDetails(object monster)
    {
        object? nextMove = GetMember(monster, "NextMove");
        object? stateMachine = GetMember(monster, "MoveStateMachine");
        object? monsterRng = GetMember(monster, "_rng");

        JsonObject obj = new()
        {
            ["id"] = FormatModelId(monster),
            ["entry"] = FormatModelEntry(monster),
            ["min_initial_hp"] = GetInt(monster, "MinInitialHp"),
            ["max_initial_hp"] = GetInt(monster, "MaxInitialHp"),
            ["spawned_this_turn"] = GetBool(monster, "SpawnedThisTurn"),
            ["is_performing_move"] = GetBool(monster, "IsPerformingMove"),
            ["intends_to_attack"] = GetBool(monster, "IntendsToAttack"),
            ["next_move"] = ExtractMoveState(nextMove),
            ["move_state_machine"] = ExtractMonsterMoveStateMachine(stateMachine)
        };

        if (monsterRng != null)
        {
            obj["rng"] = ExtractRng(monsterRng);
        }

        JsonObject? customFields = InspectCustomDeclaredFields(monster, stopAtBaseType: null, maxDepth: 2);
        if (customFields != null)
        {
            obj["custom_fields"] = customFields;
        }

        return obj;
    }

    public static JsonObject? ExtractMoveState(object? moveState)
    {
        if (moveState == null)
        {
            return null;
        }
        JsonObject obj = new()
        {
            ["id"] = GetString(moveState, "Id") ?? GetString(moveState, "StateId"),
            ["is_move"] = GetBool(moveState, "IsMove"),
            ["can_transition_away"] = GetBool(moveState, "CanTransitionAway"),
            ["follow_up_state_id"] = GetString(moveState, "FollowUpStateId")
        };

        JsonArray intentsArr = new();
        if (GetMember(moveState, "Intents") is IEnumerable intents)
        {
            foreach (object? intent in intents)
            {
                if (intent != null)
                {
                    JsonObject intentObj = new()
                    {
                        ["class"] = intent.GetType().Name,
                        ["intent_type"] = GetString(intent, "IntentType"),
                        ["repeats"] = GetInt(intent, "Repeats")
                    };
                    JsonObject? intentFields = InspectCustomDeclaredFields(intent, stopAtBaseType: null, maxDepth: 1);
                    if (intentFields != null)
                    {
                        intentObj["fields"] = intentFields;
                    }
                    intentsArr.Add(intentObj);
                }
            }
        }
        obj["intents"] = intentsArr;
        return obj;
    }

    public static JsonObject? ExtractMonsterMoveStateMachine(object? stateMachine)
    {
        if (stateMachine == null)
        {
            return null;
        }
        object? currentState = GetMember(stateMachine, "_currentState");
        object? initialState = GetMember(stateMachine, "_initialState");

        JsonObject obj = new()
        {
            ["current_state_id"] = GetString(currentState, "Id"),
            ["current_state_type"] = currentState?.GetType().Name,
            ["initial_state_id"] = GetString(initialState, "Id"),
            ["performed_first_move"] = GetBool(stateMachine, "_performedFirstMove")
        };

        JsonArray stateLogArr = new();
        if (GetMember(stateMachine, "StateLog") is IEnumerable stateLog)
        {
            foreach (object? st in stateLog)
            {
                if (st != null)
                {
                    stateLogArr.Add(JsonValue.Create(GetString(st, "Id") ?? st.ToString()));
                }
            }
        }
        obj["state_log"] = stateLogArr;

        return obj;
    }

    public static JsonObject ExtractPlayerCombatState(object player, int slotIndex)
    {
        object? pcs = GetMember(player, "PlayerCombatState");
        object? osty = GetMember(player, "Osty");

        JsonObject obj = new()
        {
            ["slot_index"] = slotIndex,
            ["player_net_id"] = GetULong(player, "NetId")?.ToString(CultureInfo.InvariantCulture),
            ["character_id"] = FormatModelId(GetMember(player, "Character")),
            ["creature_combat_id"] = GetUInt(GetMember(player, "Creature"), "CombatId"),
            ["turn_number"] = GetInt(pcs, "TurnNumber") ?? 0,
            ["phase"] = GetString(pcs, "Phase") ?? "None",
            ["energy"] = GetInt(pcs, "Energy") ?? 0,
            ["max_energy"] = GetInt(pcs, "MaxEnergy") ?? GetInt(player, "MaxEnergy"),
            ["stars"] = GetInt(pcs, "Stars") ?? 0,
            ["osty_combat_id"] = GetUInt(osty, "CombatId"),
            ["is_osty_alive"] = GetBool(player, "IsOstyAlive") ?? false,
            ["available_arrow_count"] = GetInt(pcs, "AvailableArrowCount") ?? 0
        };

        if (pcs != null)
        {
            //Pets
            JsonArray petsArr = new();
            if (GetMember(pcs, "Pets") is IEnumerable pets)
            {
                foreach (object? pet in pets)
                {
                    if (pet != null)
                    {
                        petsArr.Add(new JsonObject
                        {
                            ["combat_id"] = GetUInt(pet, "CombatId"),
                            ["model_id"] = FormatModelId(pet),
                            ["current_hp"] = GetInt(pet, "CurrentHp"),
                            ["max_hp"] = GetInt(pet, "MaxHp"),
                            ["block"] = GetInt(pet, "Block"),
                            ["is_alive"] = GetBool(pet, "IsAlive")
                        });
                    }
                }
            }
            obj["pets"] = petsArr;

            // 5 Combat Piles
            JsonObject pilesObj = new()
            {
                ["Hand"] = ExtractCardPile(GetMember(pcs, "Hand"), inCombat: true),
                ["Draw"] = ExtractCardPile(GetMember(pcs, "DrawPile"), inCombat: true),
                ["Discard"] = ExtractCardPile(GetMember(pcs, "DiscardPile"), inCombat: true),
                ["Exhaust"] = ExtractCardPile(GetMember(pcs, "ExhaustPile"), inCombat: true),
                ["Play"] = ExtractCardPile(GetMember(pcs, "PlayPile"), inCombat: true)
            };
            obj["piles"] = pilesObj;

            // Orbs
            object? orbQueue = GetMember(pcs, "OrbQueue");
            JsonObject orbsObj = new()
            {
                ["capacity"] = GetInt(orbQueue, "Capacity") ?? 0
            };
            JsonArray orbsList = new();
            if (GetMember(orbQueue, "Orbs") is IEnumerable orbs)
            {
                int oIdx = 0;
                foreach (object? orb in orbs)
                {
                    if (orb != null)
                    {
                        JsonObject orbItem = new()
                        {
                            ["index"] = oIdx++,
                            ["id"] = FormatModelId(orb),
                            ["entry"] = FormatModelEntry(orb),
                            ["passive_val"] = GetDecimal(orb, "PassiveVal"),
                            ["evoke_val"] = GetDecimal(orb, "EvokeVal")
                        };
                        JsonObject? orbFields = InspectCustomDeclaredFields(orb, stopAtBaseType: null, maxDepth: 1);
                        if (orbFields != null)
                        {
                            orbItem["custom_fields"] = orbFields;
                        }
                        orbsList.Add(orbItem);
                    }
                }
            }
            orbsObj["orbs"] = orbsList;
            obj["orb_queue"] = orbsObj;

            // Fool Arrows
            JsonArray arrowsArr = new();
            if (GetMember(pcs, "Arrows") is IEnumerable arrows)
            {
                int aIdx = 0;
                foreach (object? arrow in arrows)
                {
                    if (arrow != null)
                    {
                        arrowsArr.Add(new JsonObject
                        {
                            ["index"] = aIdx++,
                            ["status"] = GetString(arrow, "Status"),
                            ["is_available"] = GetBool(arrow, "IsAvailable"),
                            ["destroy_after_impaled"] = GetBool(arrow, "DestroyAfterImpaled")
                        });
                    }
                }
            }
            obj["arrows"] = arrowsArr;
        }

        return obj;
    }

    public static JsonArray ExtractCardPile(object? cardPile, bool inCombat)
    {
        JsonArray arr = new();
        if (GetMember(cardPile, "Cards") is IEnumerable cards)
        {
            int idx = 0;
            foreach (object? card in cards)
            {
                if (card != null)
                {
                    arr.Add(ExtractCardState(card, idx++, inCombat));
                }
            }
        }
        return arr;
    }

    public static JsonObject ExtractCardState(object card, int index, bool inCombat)
    {
        object? energyCost = GetMember(card, "EnergyCost");
        object? affliction = GetMember(card, "Affliction");
        object? enchantment = GetMember(card, "Enchantment");
        object? serializableCard = InvokeMethod(card, "ToSerializable");

        uint? combatCardIdx = null;
        if (inCombat)
        {
            object? netCombatCardDb = GetStaticMember("MegaCrit.Sts2.Core.GameActions.Multiplayer.NetCombatCardDb", "Instance");
            if (netCombatCardDb != null)
            {
                object? idVal = InvokeMethod(netCombatCardDb, "GetCardId", card);
                if (idVal is uint cid)
                {
                    combatCardIdx = cid;
                }
            }
        }

        JsonObject obj = new()
        {
            ["index"] = index,
            ["combat_card_index"] = combatCardIdx,
            ["id"] = FormatModelId(card),
            ["entry"] = FormatModelEntry(card),
            ["type"] = GetString(card, "Type"),
            ["rarity"] = GetString(card, "Rarity"),
            ["target_type"] = GetString(card, "TargetType"),
            ["current_upgrade_level"] = GetInt(card, "CurrentUpgradeLevel"),
            ["max_upgrade_level"] = GetInt(card, "MaxUpgradeLevel"),
            ["is_upgraded"] = GetBool(card, "IsUpgraded"),
            ["base_replay_count"] = GetInt(card, "BaseReplayCount"),
            ["extra_replay_this_turn"] = GetInt(card, "ExtraReplayThisTurn"),
            ["exhaust_on_next_play"] = GetBool(card, "ExhaustOnNextPlay"),
            ["should_retain_this_turn"] = GetBool(card, "ShouldRetainThisTurn"),
            ["has_single_turn_retain"] = GetBool(card, "_hasSingleTurnRetain"),
            ["is_sly_this_turn"] = GetBool(card, "IsSlyThisTurn"),
            ["has_single_turn_sly"] = GetBool(card, "_hasSingleTurnSly"),
            ["is_dupe"] = GetBool(card, "_isDupe"),
            ["floor_added_to_deck"] = GetInt(card, "_floorAddedToDeck")
        };

        // Energy Cost details (including local modifiers & global modified cost)
        if (energyCost != null)
        {
            bool costsX = GetBool(energyCost, "CostsX") ?? false;
            JsonObject costObj = new()
            {
                ["canonical"] = GetInt(energyCost, "Canonical"),
                ["base"] = GetInt(energyCost, "_base"),
                ["costs_x"] = costsX,
                ["captured_x_value"] = costsX ? GetInt(energyCost, "_capturedXValue") : null,
                ["has_local_modifiers"] = GetBool(energyCost, "HasLocalModifiers")
            };

            if (inCombat)
            {
                if (InvokeMethod(energyCost, "GetAmountToSpend") is int amountToSpend)
                {
                    costObj["amount_to_spend"] = amountToSpend;
                }
            }

            JsonArray localModsArr = new();
            if (GetMember(energyCost, "_localModifiers") is IEnumerable localMods)
            {
                foreach (object? mod in localMods)
                {
                    if (mod != null)
                    {
                        localModsArr.Add(ConvertArbitraryValueToJson(mod, 2));
                    }
                }
            }
            costObj["local_modifiers"] = localModsArr;
            obj["energy_cost"] = costObj;
        }

        // Star Cost details (Regent mechanics)
        JsonObject starCostObj = new()
        {
            ["canonical"] = GetInt(card, "CanonicalStarCost"),
            ["base"] = GetInt(card, "BaseStarCost"),
            ["current"] = GetInt(card, "CurrentStarCost"),
            ["costs_x"] = GetBool(card, "HasStarCostX"),
            ["last_stars_spent"] = GetInt(card, "LastStarsSpent")
        };
        JsonArray tempStarArr = new();
        if (GetMember(card, "_temporaryStarCosts") is IEnumerable tempStarCosts)
        {
            foreach (object? tsc in tempStarCosts)
            {
                if (tsc != null)
                {
                    tempStarArr.Add(ConvertArbitraryValueToJson(tsc, 2));
                }
            }
        }
        starCostObj["temporary_star_costs"] = tempStarArr;
        obj["star_cost"] = starCostObj;

        // Keywords & Tags
        JsonArray keywordsArr = new();
        if (GetMember(card, "Keywords") is IEnumerable keywords)
        {
            foreach (object? kw in keywords)
            {
                if (kw != null)
                {
                    keywordsArr.Add(JsonValue.Create(kw.ToString()));
                }
            }
        }
        obj["keywords"] = keywordsArr;

        JsonArray tagsArr = new();
        if (GetMember(card, "Tags") is IEnumerable tags)
        {
            foreach (object? tag in tags)
            {
                if (tag != null)
                {
                    tagsArr.Add(JsonValue.Create(tag.ToString()));
                }
            }
        }
        obj["tags"] = tagsArr;

        // Affliction & Enchantment
        if (affliction != null)
        {
            obj["affliction"] = new JsonObject
            {
                ["id"] = FormatModelId(affliction),
                ["amount"] = GetInt(affliction, "Amount")
            };
        }

        if (enchantment != null)
        {
            obj["enchantment"] = new JsonObject
            {
                ["id"] = FormatModelId(enchantment),
                ["amount"] = GetInt(enchantment, "Amount"),
                ["status"] = GetString(enchantment, "Status")
            };
        }

        // SavedProperties from SerializableCard
        object? savedProps = GetMember(serializableCard, "Props");
        if (savedProps != null)
        {
            obj["saved_properties"] = ExtractSavedProperties(savedProps);
        }

        // DynamicVars (only if already initialized on the card instance)
        object? dynVars = GetMember(card, "_dynamicVars");
        if (dynVars != null)
        {
            obj["dynamic_vars"] = ExtractDynamicVarSet(dynVars);
        }

        JsonObject? customFields = InspectCustomDeclaredFields(card, stopAtBaseType: null, maxDepth: 2);
        if (customFields != null)
        {
            obj["custom_fields"] = customFields;
        }

        return obj;
    }

    public static JsonObject ExtractRelicState(object relic, int index)
    {
        object? serializableRelic = InvokeMethod(relic, "ToSerializable");
        object? savedProps = GetMember(serializableRelic, "Props");

        JsonObject obj = new()
        {
            ["index"] = index,
            ["id"] = FormatModelId(relic),
            ["entry"] = FormatModelEntry(relic),
            ["rarity"] = GetString(relic, "Rarity"),
            ["status"] = GetString(relic, "Status"),
            ["stack_count"] = GetInt(relic, "StackCount"),
            ["show_counter"] = GetBool(relic, "ShowCounter"),
            ["display_amount"] = GetInt(relic, "DisplayAmount"),
            ["is_used_up"] = GetBool(relic, "IsUsedUp"),
            ["is_wax"] = GetBool(relic, "IsWax"),
            ["is_melted"] = GetBool(relic, "IsMelted"),
            ["floor_added_to_deck"] = GetInt(relic, "FloorAddedToDeck")
        };

        if (savedProps != null)
        {
            obj["saved_properties"] = ExtractSavedProperties(savedProps);
        }

        object? dynVars = GetMember(relic, "_dynamicVars");
        if (dynVars != null)
        {
            obj["dynamic_vars"] = ExtractDynamicVarSet(dynVars);
        }

        JsonObject? customFields = InspectCustomDeclaredFields(relic, stopAtBaseType: null, maxDepth: 2);
        if (customFields != null)
        {
            obj["custom_fields"] = customFields;
        }

        return obj;
    }

    public static JsonObject ExtractPotionSlotState(object? potion, int slotIndex)
    {
        if (potion == null)
        {
            return new JsonObject
            {
                ["slot_index"] = slotIndex,
                ["has_potion"] = false,
                ["id"] = null
            };
        }
        return new JsonObject
        {
            ["slot_index"] = slotIndex,
            ["has_potion"] = true,
            ["id"] = FormatModelId(potion),
            ["entry"] = FormatModelEntry(potion),
            ["rarity"] = GetString(potion, "Rarity"),
            ["usage"] = GetString(potion, "Usage"),
            ["target_type"] = GetString(potion, "TargetType")
        };
    }

    public static JsonObject? ExtractDynamicVarSet(object? dynamicVarSet)
    {
        if (dynamicVarSet == null)
        {
            return null;
        }
        JsonObject obj = new();
        if (GetMember(dynamicVarSet, "Values") is IEnumerable values)
        {
            foreach (object? dv in values)
            {
                if (dv == null)
                {
                    continue;
                }
                string? name = GetString(dv, "Name");
                if (string.IsNullOrEmpty(name))
                {
                    continue;
                }
                obj[name] = new JsonObject
                {
                    ["base"] = GetDecimal(dv, "BaseValue"),
                    ["enchanted"] = GetDecimal(dv, "EnchantedValue"),
                    ["preview"] = GetDecimal(dv, "PreviewValue")
                };
            }
        }
        return obj.Count > 0 ? obj : null;
    }

    public static JsonObject? ExtractSavedProperties(object? savedProps)
    {
        if (savedProps == null)
        {
            return null;
        }
        JsonObject obj = new();
        ExtractSavedPropList(savedProps, "ints", obj);
        ExtractSavedPropList(savedProps, "bools", obj);
        ExtractSavedPropList(savedProps, "strings", obj);
        ExtractSavedPropList(savedProps, "intArrays", obj);
        ExtractSavedPropList(savedProps, "modelIds", obj);
        ExtractSavedPropList(savedProps, "cards", obj);
        ExtractSavedPropList(savedProps, "cardArrays", obj);
        return obj.Count > 0 ? obj : null;
    }

    private static void ExtractSavedPropList(object savedProps, string fieldName, JsonObject target)
    {
        if (GetMember(savedProps, fieldName) is IEnumerable list)
        {
            JsonObject bucket = new();
            foreach (object? item in list)
            {
                if (item == null)
                {
                    continue;
                }
                string? name = GetString(item, "name");
                object? val = GetMember(item, "value");
                if (!string.IsNullOrEmpty(name))
                {
                    bucket[name] = ConvertArbitraryValueToJson(val, 2);
                }
            }
            if (bucket.Count > 0)
            {
                target[fieldName] = bucket;
            }
        }
    }

    // ========================================================================
    // RNG & Odds Extraction (64-bit Decimal Strings + IEEE-754 Float32 Bits)
    // ========================================================================

    public static JsonObject? ExtractRunRngSet(object? runRngSet)
    {
        if (runRngSet == null)
        {
            return null;
        }
        object? serializable = InvokeMethod(runRngSet, "ToSerializable") ?? runRngSet;
        ulong? seed = GetULong(runRngSet, "Seed") ?? GetULong(serializable, "Seed");

        JsonObject obj = new()
        {
            ["seed_u64"] = seed?.ToString(CultureInfo.InvariantCulture),
            ["string_seed"] = GetString(runRngSet, "StringSeed")
        };

        JsonObject rngsMap = new();
        if (GetMember(serializable, "Rngs") is IDictionary dict)
        {
            foreach (DictionaryEntry entry in dict)
            {
                string key = entry.Key?.ToString() ?? "unknown";
                rngsMap[key] = ExtractSerializableRng(entry.Value);
            }
        }
        obj["rngs"] = rngsMap;
        return obj;
    }

    public static JsonObject? ExtractPlayerRngSet(object? playerRngSet)
    {
        if (playerRngSet == null)
        {
            return null;
        }
        object? serializable = InvokeMethod(playerRngSet, "ToSerializable") ?? playerRngSet;
        JsonObject rngsMap = new();
        if (GetMember(serializable, "Rngs") is IDictionary dict)
        {
            foreach (DictionaryEntry entry in dict)
            {
                string key = entry.Key?.ToString() ?? "unknown";
                rngsMap[key] = ExtractSerializableRng(entry.Value);
            }
        }
        return rngsMap;
    }

    public static JsonObject? ExtractRng(object? rng)
    {
        if (rng == null)
        {
            return null;
        }
        object? serializable = InvokeMethod(rng, "ToSerializable") ?? rng;
        return ExtractSerializableRng(serializable);
    }

    public static JsonObject? ExtractSerializableRng(object? serRng)
    {
        if (serRng == null)
        {
            return null;
        }
        ulong s0 = GetULong(serRng, "state0") ?? 0UL;
        ulong s1 = GetULong(serRng, "state1") ?? 0UL;
        ulong s2 = GetULong(serRng, "state2") ?? 0UL;
        ulong s3 = GetULong(serRng, "state3") ?? 0UL;
        int counter = GetInt(serRng, "counter") ?? 0;

        return new JsonObject
        {
            ["counter"] = counter,
            ["s0"] = s0.ToString(CultureInfo.InvariantCulture),
            ["s1"] = s1.ToString(CultureInfo.InvariantCulture),
            ["s2"] = s2.ToString(CultureInfo.InvariantCulture),
            ["s3"] = s3.ToString(CultureInfo.InvariantCulture)
        };
    }

    public static JsonObject? ExtractRunOddsSet(object? runOddsSet)
    {
        if (runOddsSet == null)
        {
            return null;
        }
        object? ser = InvokeMethod(runOddsSet, "ToSerializable") ?? runOddsSet;
        object? unknownMapPoint = GetMember(ser, "UnknownMapPoint") ?? GetMember(runOddsSet, "UnknownMapPoint");
        if (unknownMapPoint == null)
        {
            return null;
        }
        return new JsonObject
        {
            ["monster"] = CreateFloatWithBits(GetFloat(unknownMapPoint, "MonsterOdds")),
            ["elite"] = CreateFloatWithBits(GetFloat(unknownMapPoint, "EliteOdds")),
            ["event"] = CreateFloatWithBits(GetFloat(unknownMapPoint, "EventOdds")),
            ["shop"] = CreateFloatWithBits(GetFloat(unknownMapPoint, "ShopOdds")),
            ["treasure"] = CreateFloatWithBits(GetFloat(unknownMapPoint, "TreasureOdds"))
        };
    }

    public static JsonObject? ExtractPlayerOddsSet(object? playerOddsSet)
    {
        if (playerOddsSet == null)
        {
            return null;
        }
        object? ser = InvokeMethod(playerOddsSet, "ToSerializable") ?? playerOddsSet;
        float? cardRarity = GetFloat(ser, "CardRarityOddsValue")
                            ?? GetFloat(GetMember(playerOddsSet, "CardRarity"), "CurrentValue");
        float? potionReward = GetFloat(ser, "PotionRewardOddsValue")
                              ?? GetFloat(GetMember(playerOddsSet, "PotionReward"), "CurrentValue");

        return new JsonObject
        {
            ["card_rarity_odds"] = CreateFloatWithBits(cardRarity),
            ["potion_reward_odds"] = CreateFloatWithBits(potionReward)
        };
    }

    private static JsonObject? CreateFloatWithBits(float? val)
    {
        if (!val.HasValue)
        {
            return null;
        }
        uint bits = BitConverter.SingleToUInt32Bits(val.Value);
        return new JsonObject
        {
            ["value"] = val.Value,
            ["f32_bits"] = bits,
            ["f32_hex"] = "0x" + bits.ToString("x8", CultureInfo.InvariantCulture)
        };
    }

    public static JsonObject? ExtractRelicGrabBag(object? grabBag)
    {
        if (grabBag == null)
        {
            return null;
        }
        object? ser = InvokeMethod(grabBag, "ToSerializable") ?? grabBag;
        JsonObject obj = new();
        if (GetMember(ser, "RelicIdLists") is IDictionary dict)
        {
            foreach (DictionaryEntry entry in dict)
            {
                string rarityKey = entry.Key?.ToString() ?? "unknown";
                JsonArray ids = new();
                if (entry.Value is IEnumerable list)
                {
                    foreach (object? id in list)
                    {
                        ids.Add(JsonValue.Create(FormatModelId(id)));
                    }
                }
                obj[rarityKey] = ids;
            }
        }
        return obj;
    }

    // ========================================================================
    // ActionQueueSet, GameAction, PlayerChoice, and NetFullCombatState
    // ========================================================================

    public static JsonObject? ExtractActionQueues(object runMgr)
    {
        object? queueSet = GetMember(runMgr, "ActionQueueSet");
        object? executor = GetMember(runMgr, "ActionExecutor");
        if (queueSet == null)
        {
            return null;
        }

        JsonObject obj = new()
        {
            ["next_action_id"] = GetUInt(queueSet, "NextActionId"),
            ["is_empty"] = GetBool(queueSet, "IsEmpty"),
            ["was_reset"] = GetBool(queueSet, "WasReset"),
            ["is_in_combat"] = GetBool(queueSet, "_isInCombat"),
            ["executor_is_paused"] = GetBool(executor, "IsPaused"),
            ["executor_is_running"] = GetBool(executor, "IsRunning"),
            ["currently_running_action"] = ExtractGameAction(GetMember(executor, "CurrentlyRunningAction"))
        };

        JsonArray queuesArr = new();
        if (GetMember(queueSet, "_actionQueues") is IEnumerable queues)
        {
            foreach (object? q in queues)
            {
                if (q == null)
                {
                    continue;
                }
                JsonObject qObj = new()
                {
                    ["owner_id"] = GetULong(q, "ownerId")?.ToString(CultureInfo.InvariantCulture),
                    ["is_paused"] = GetBool(q, "isPaused"),
                    ["is_cancelling_play_card_actions"] = GetBool(q, "IsCancellingPlayCardActions"),
                    ["is_cancelling_player_driven_combat_actions"] = GetBool(q, "isCancellingPlayerDrivenCombatActions"),
                    ["is_cancelling_combat_actions"] = GetBool(q, "isCancellingCombatActions"),
                    ["action_cancelling_play_card_id"] = GetUInt(GetMember(q, "actionCancellingPlayCardActions"), "Id")
                };

                JsonArray actionsArr = new();
                if (GetMember(q, "actions") is IEnumerable actions)
                {
                    foreach (object? act in actions)
                    {
                        if (act != null)
                        {
                            actionsArr.Add(ExtractGameAction(act));
                        }
                    }
                }
                qObj["queued_actions"] = actionsArr;
                queuesArr.Add(qObj);
            }
        }
        obj["player_queues"] = queuesArr;

        JsonArray waitingArr = new();
        if (GetMember(queueSet, "_actionsWaitingForResumption") is IEnumerable waiting)
        {
            foreach (object? w in waiting)
            {
                if (w != null)
                {
                    waitingArr.Add(new JsonObject
                    {
                        ["old_id"] = GetUInt(w, "oldId"),
                        ["new_id"] = GetUInt(w, "newId")
                    });
                }
            }
        }
        obj["actions_waiting_for_resumption"] = waitingArr;

        return obj;
    }

    public static JsonObject ExtractSynchronizerIds(object runMgr)
    {
        object? choiceSync = GetMember(runMgr, "PlayerChoiceSynchronizer");
        object? rewardsSetSync = GetMember(runMgr, "RewardsSetSynchronizer");
        object? actionQueueSync = GetMember(runMgr, "ActionQueueSynchronizer");
        object? checksumTracker = GetMember(runMgr, "ChecksumTracker");

        JsonObject obj = new()
        {
            ["next_hook_id"] = GetUInt(actionQueueSync, "NextHookId"),
            ["next_checksum_id"] = GetUInt(checksumTracker, "NextId")
        };

        JsonArray choiceIds = new();
        if (GetMember(choiceSync, "ChoiceIds") is IEnumerable cids)
        {
            foreach (object? id in cids)
            {
                if (id is uint u)
                {
                    choiceIds.Add(JsonValue.Create(u));
                }
            }
        }
        obj["choice_ids"] = choiceIds;

        JsonArray rewardIds = new();
        if (InvokeMethod(rewardsSetSync, "GetNextRewardIds") is IEnumerable rids)
        {
            foreach (object? id in rids)
            {
                if (id is int i)
                {
                    rewardIds.Add(JsonValue.Create(i));
                }
            }
        }
        obj["reward_ids"] = rewardIds;

        return obj;
    }

    public static JsonObject? ExtractGameAction(object? action)
    {
        if (action == null)
        {
            return null;
        }
        Type t = action.GetType();
        bool recordable = GetBool(action, "RecordableToReplay") ?? false;

        JsonObject obj = new()
        {
            ["action_id"] = GetUInt(action, "Id"),
            ["action_class"] = t.Name,
            ["action_type"] = GetString(action, "ActionType"),
            ["state"] = GetString(action, "State"),
            ["owner_id"] = GetULong(action, "OwnerId")?.ToString(CultureInfo.InvariantCulture),
            ["recordable_to_replay"] = recordable,
            ["summary"] = action.ToString()
        };

        // Specific GameAction payloads
        switch (t.Name)
        {
            case "PlayCardAction":
            {
                object? netCard = GetMember(action, "NetCombatCard");
                object? cardModel = GetMember(action, "_card") ?? InvokeMethod(netCard, "ToCardModelOrNull");
                obj["card_model_id"] = FormatModelId(GetMember(action, "CardModelId")) ?? FormatModelId(cardModel);
                obj["combat_card_index"] = GetUInt(netCard, "CombatCardIndex");
                obj["target_id"] = GetUInt(action, "TargetId");
                if (cardModel != null)
                {
                    obj["card_snapshot"] = ExtractCardState(cardModel, 0, inCombat: true);
                }
                break;
            }
            case "UsePotionAction":
            {
                obj["potion_index"] = GetUInt(action, "PotionIndex");
                obj["target_id"] = GetUInt(action, "TargetId");
                obj["target_player_id"] = GetULong(action, "TargetPlayerId")?.ToString(CultureInfo.InvariantCulture);
                obj["was_enqueued_in_combat"] = GetBool(action, "WasEnqueuedInCombat");
                break;
            }
            case "DiscardPotionGameAction":
            {
                obj["potion_index"] = GetUInt(action, "_potionIndex") ?? GetUInt(action, "PotionIndex");
                obj["was_enqueued_in_combat"] = GetBool(action, "_wasEnqueuedInCombat");
                break;
            }
            case "GenericHookGameAction":
            {
                object? choiceCtx = GetMember(action, "ChoiceContext");
                obj["hook_id"] = GetUInt(action, "HookId");
                obj["choice_source"] = GetString(choiceCtx, "Source");
                obj["last_involved_model"] = FormatModelId(GetMember(choiceCtx, "LastInvolvedModel"));
                break;
            }
            case "MoveToMapCoordAction":
            {
                obj["destination"] = ExtractMapCoord(GetMember(action, "_destination"));
                break;
            }
            case "VoteForMapCoordAction":
            {
                obj["source"] = ConvertArbitraryValueToJson(GetMember(action, "_source"), 2);
                obj["destination"] = ConvertArbitraryValueToJson(GetMember(action, "_destination"), 2);
                break;
            }
            case "PickRelicAction":
            {
                obj["relic_index"] = GetInt(action, "_relicIndex");
                break;
            }
            default:
            {
                JsonObject? extra = InspectCustomDeclaredFields(action, stopAtBaseType: null, maxDepth: 2);
                if (extra != null)
                {
                    obj["fields"] = extra;
                }
                break;
            }
        }

        if (recordable)
        {
            object? netAction = InvokeMethod(action, "ToNetAction");
            if (netAction != null)
            {
                obj["net_action"] = ConvertArbitraryValueToJson(netAction, 2);
            }
        }

        return obj;
    }

    public static JsonObject ExtractPlayerChoiceResult(object? player, uint choiceId, object? netResult)
    {
        JsonObject obj = new()
        {
            ["player_net_id"] = GetULong(player, "NetId")?.ToString(CultureInfo.InvariantCulture),
            ["character_id"] = FormatModelId(GetMember(player, "Character")),
            ["choice_id"] = choiceId,
            ["choice_type"] = GetString(netResult, "type")
        };

        if (netResult == null)
        {
            return obj;
        }

        if (GetMember(netResult, "indexes") is IEnumerable indexes)
        {
            JsonArray arr = new();
            foreach (object? idx in indexes)
            {
                if (idx is int i)
                {
                    arr.Add(JsonValue.Create(i));
                }
            }
            obj["indexes"] = arr;
        }

        if (GetMember(netResult, "canonicalCards") is IEnumerable canonicalCards)
        {
            JsonArray arr = new();
            foreach (object? card in canonicalCards)
            {
                if (card != null)
                {
                    arr.Add(JsonValue.Create(FormatModelId(card)));
                }
            }
            obj["canonical_cards"] = arr;
        }

        if (GetMember(netResult, "combatCards") is IEnumerable combatCards)
        {
            JsonArray arr = new();
            foreach (object? netCard in combatCards)
            {
                if (netCard != null)
                {
                    object? resolved = InvokeMethod(netCard, "ToCardModelOrNull");
                    arr.Add(new JsonObject
                    {
                        ["combat_card_index"] = GetUInt(netCard, "CombatCardIndex"),
                        ["card_id"] = FormatModelId(resolved),
                        ["upgrade_level"] = GetInt(resolved, "CurrentUpgradeLevel")
                    });
                }
            }
            obj["combat_cards"] = arr;
        }

        if (GetMember(netResult, "deckCards") is IEnumerable deckCards)
        {
            obj["deck_cards"] = ConvertArbitraryValueToJson(deckCards, 2);
        }

        if (GetMember(netResult, "mutableCards") is IEnumerable mutableCards)
        {
            obj["mutable_cards"] = ConvertArbitraryValueToJson(mutableCards, 3);
            obj["mutable_card_owner"] = GetULong(netResult, "mutableCardOwner")?.ToString(CultureInfo.InvariantCulture);
        }

        if (GetULong(netResult, "playerId") is ulong targetPid)
        {
            obj["target_player_id"] = targetPid.ToString(CultureInfo.InvariantCulture);
        }

        return obj;
    }

    // ========================================================================
    // All 18 CombatHistoryEntry Types Extraction
    // ========================================================================

    public static JsonObject ExtractCombatHistoryEntry(object entry, int historyIndex)
    {
        Type t = entry.GetType();
        object? actor = GetMember(entry, "Actor");

        JsonObject obj = new()
        {
            ["history_index"] = historyIndex,
            ["entry_type"] = t.Name,
            ["round_number"] = GetInt(entry, "RoundNumber"),
            ["current_side"] = GetString(entry, "CurrentSide"),
            ["description"] = GetString(entry, "Description"),
            ["human_readable"] = GetString(entry, "HumanReadableString"),
            ["actor"] = actor != null ? new JsonObject
            {
                ["combat_id"] = GetUInt(actor, "CombatId"),
                ["model_id"] = FormatModelId(actor),
                ["side"] = GetString(actor, "Side"),
                ["is_player"] = GetBool(actor, "IsPlayer"),
                ["player_net_id"] = GetULong(GetMember(actor, "Player"), "NetId")?.ToString(CultureInfo.InvariantCulture)
            } : null
        };

        if (GetMember(entry, "_playerTurnNumbers") is IDictionary turnNums)
        {
            JsonObject turnsObj = new();
            foreach (DictionaryEntry kv in turnNums)
            {
                string k = kv.Key?.ToString() ?? "0";
                turnsObj[k] = ConvertArbitraryValueToJson(kv.Value, 1);
            }
            obj["player_turn_numbers"] = turnsObj;
        }

        switch (t.Name)
        {
            case "CardPlayStartedEntry":
            case "CardPlayFinishedEntry":
            {
                object? cardPlay = GetMember(entry, "CardPlay");
                obj["was_ethereal"] = GetBool(entry, "WasEthereal");
                obj["card_play"] = ExtractCardPlay(cardPlay);
                break;
            }
            case "CardDrawnEntry":
            {
                object? card = GetMember(entry, "Card");
                obj["from_hand_draw"] = GetBool(entry, "FromHandDraw");
                obj["card"] = card != null ? ExtractCardState(card, 0, inCombat: true) : null;
                break;
            }
            case "CardDiscardedEntry":
            case "CardExhaustedEntry":
            {
                object? card = GetMember(entry, "Card");
                obj["card"] = card != null ? ExtractCardState(card, 0, inCombat: true) : null;
                break;
            }
            case "CardGeneratedEntry":
            {
                object? card = GetMember(entry, "Card");
                object? creator = GetMember(entry, "Creator");
                obj["creator_net_id"] = GetULong(creator, "NetId")?.ToString(CultureInfo.InvariantCulture);
                obj["card"] = card != null ? ExtractCardState(card, 0, inCombat: true) : null;
                break;
            }
            case "CardAfflictedEntry":
            {
                object? card = GetMember(entry, "Card");
                object? affliction = GetMember(entry, "Affliction");
                obj["affliction_id"] = FormatModelId(affliction);
                obj["affliction_amount"] = GetInt(affliction, "Amount");
                obj["card"] = card != null ? ExtractCardState(card, 0, inCombat: true) : null;
                break;
            }
            case "CreatureAttackedEntry":
            {
                JsonArray resultsArr = new();
                if (GetMember(entry, "DamageResults") is IEnumerable results)
                {
                    foreach (object? dr in results)
                    {
                        if (dr != null)
                        {
                            resultsArr.Add(ExtractDamageResult(dr));
                        }
                    }
                }
                obj["damage_results"] = resultsArr;
                break;
            }
            case "DamageReceivedEntry":
            {
                object? dr = GetMember(entry, "Result");
                object? dealer = GetMember(entry, "Dealer");
                object? receiver = GetMember(entry, "Receiver");
                object? cardSource = GetMember(entry, "CardSource");
                obj["receiver_combat_id"] = GetUInt(receiver, "CombatId");
                obj["receiver_model_id"] = FormatModelId(receiver);
                obj["dealer_combat_id"] = GetUInt(dealer, "CombatId");
                obj["dealer_model_id"] = FormatModelId(dealer);
                obj["card_source_id"] = FormatModelId(cardSource);
                obj["damage_result"] = dr != null ? ExtractDamageResult(dr) : null;
                break;
            }
            case "BlockGainedEntry":
            {
                object? receiver = GetMember(entry, "Receiver");
                object? cardPlay = GetMember(entry, "CardPlay");
                obj["receiver_combat_id"] = GetUInt(receiver, "CombatId");
                obj["receiver_model_id"] = FormatModelId(receiver);
                obj["amount"] = GetInt(entry, "Amount");
                obj["value_props"] = GetString(entry, "Props");
                obj["value_props_int"] = GetInt(entry, "Props");
                obj["card_play"] = ExtractCardPlay(cardPlay);
                break;
            }
            case "EnergySpentEntry":
            case "StarsModifiedEntry":
            case "SummonedEntry":
            {
                obj["amount"] = GetInt(entry, "Amount");
                break;
            }
            case "MonsterPerformedMoveEntry":
            {
                object? monster = GetMember(entry, "Monster");
                object? move = GetMember(entry, "Move");
                obj["monster_id"] = FormatModelId(monster);
                obj["monster_combat_id"] = GetUInt(GetMember(monster, "Creature"), "CombatId");
                obj["move"] = ExtractMoveState(move);
                JsonArray targetsArr = new();
                if (GetMember(entry, "Targets") is IEnumerable targets)
                {
                    foreach (object? tgt in targets)
                    {
                        if (tgt != null)
                        {
                            targetsArr.Add(new JsonObject
                            {
                                ["combat_id"] = GetUInt(tgt, "CombatId"),
                                ["model_id"] = FormatModelId(tgt)
                            });
                        }
                    }
                }
                obj["targets"] = targetsArr;
                break;
            }
            case "OrbChanneledEntry":
            {
                object? orb = GetMember(entry, "Orb");
                obj["orb_id"] = FormatModelId(orb);
                obj["passive_val"] = GetDecimal(orb, "PassiveVal");
                obj["evoke_val"] = GetDecimal(orb, "EvokeVal");
                break;
            }
            case "ArrowShotEntry":
            {
                object? slot = GetMember(entry, "Slot");
                obj["arrow_status"] = GetString(slot, "Status");
                obj["destroy_after_impaled"] = GetBool(slot, "DestroyAfterImpaled");
                break;
            }
            case "PotionUsedEntry":
            {
                object? potion = GetMember(entry, "Potion");
                object? target = GetMember(entry, "Target");
                obj["potion_id"] = FormatModelId(potion);
                obj["target_combat_id"] = GetUInt(target, "CombatId");
                obj["target_model_id"] = FormatModelId(target);
                break;
            }
            case "PowerReceivedEntry":
            {
                object? power = GetMember(entry, "Power");
                object? applier = GetMember(entry, "Applier");
                obj["power_id"] = FormatModelId(power);
                obj["amount"] = GetDecimal(entry, "Amount");
                obj["power_current_amount"] = GetInt(power, "Amount");
                obj["applier_combat_id"] = GetUInt(applier, "CombatId");
                obj["applier_model_id"] = FormatModelId(applier);
                break;
            }
        }

        return obj;
    }

    public static JsonObject? ExtractCardPlay(object? cardPlay)
    {
        if (cardPlay == null)
        {
            return null;
        }
        object? card = GetMember(cardPlay, "Card");
        object? player = GetMember(cardPlay, "Player");
        object? target = GetMember(cardPlay, "Target");
        object? resources = GetMember(cardPlay, "Resources");

        return new JsonObject
        {
            ["card_id"] = FormatModelId(card),
            ["card_upgrade_level"] = GetInt(card, "CurrentUpgradeLevel"),
            ["player_net_id"] = GetULong(player, "NetId")?.ToString(CultureInfo.InvariantCulture),
            ["target_combat_id"] = GetUInt(target, "CombatId"),
            ["target_model_id"] = FormatModelId(target),
            ["result_pile"] = GetString(cardPlay, "ResultPile"),
            ["is_auto_play"] = GetBool(cardPlay, "IsAutoPlay"),
            ["play_index"] = GetInt(cardPlay, "PlayIndex"),
            ["play_count"] = GetInt(cardPlay, "PlayCount"),
            ["is_first_in_series"] = GetBool(cardPlay, "IsFirstInSeries"),
            ["is_last_in_series"] = GetBool(cardPlay, "IsLastInSeries"),
            ["resources"] = resources != null ? new JsonObject
            {
                ["energy_spent"] = GetInt(resources, "EnergySpent"),
                ["energy_value"] = GetInt(resources, "EnergyValue"),
                ["stars_spent"] = GetInt(resources, "StarsSpent"),
                ["star_value"] = GetInt(resources, "StarValue")
            } : null
        };
    }

    public static JsonObject ExtractDamageResult(object dr)
    {
        object? receiver = GetMember(dr, "Receiver");
        object? originalTarget = GetMember(dr, "OriginalTarget");
        return new JsonObject
        {
            ["receiver_combat_id"] = GetUInt(receiver, "CombatId"),
            ["receiver_model_id"] = FormatModelId(receiver),
            ["original_target_combat_id"] = GetUInt(originalTarget, "CombatId"),
            ["original_target_model_id"] = FormatModelId(originalTarget),
            ["value_props"] = GetString(dr, "Props"),
            ["value_props_int"] = GetInt(dr, "Props"),
            ["intended_hp_loss"] = GetInt(dr, "IntendedHpLoss"),
            ["blocked_damage"] = GetInt(dr, "BlockedDamage"),
            ["unblocked_damage"] = GetInt(dr, "UnblockedDamage"),
            ["overkill_damage"] = GetInt(dr, "OverkillDamage"),
            ["total_damage"] = GetInt(dr, "TotalDamage"),
            ["was_block_broken"] = GetBool(dr, "WasBlockBroken"),
            ["was_fully_blocked"] = GetBool(dr, "WasFullyBlocked")
        };
    }

    public static JsonObject? ExtractNetFullCombatState(object? fullState)
    {
        if (fullState == null)
        {
            return null;
        }
        return ConvertArbitraryValueToJson(fullState, 5) as JsonObject;
    }

    // ========================================================================
    // Map, Rooms, and Canonical Digest Helpers
    // ========================================================================

    public static JsonObject? ExtractMapCoord(object? mapCoord)
    {
        if (mapCoord == null)
        {
            return null;
        }
        return new JsonObject
        {
            ["col"] = GetInt(mapCoord, "col") ?? GetInt(mapCoord, "Col"),
            ["row"] = GetInt(mapCoord, "row") ?? GetInt(mapCoord, "Row")
        };
    }

    public static JsonArray ExtractMapCoordList(object? coordsEnumerable)
    {
        JsonArray arr = new();
        if (coordsEnumerable is IEnumerable list)
        {
            foreach (object? item in list)
            {
                if (item != null)
                {
                    arr.Add(ExtractMapCoord(item));
                }
            }
        }
        return arr;
    }

    public static JsonArray ExtractRoomStack(object? roomsEnumerable)
    {
        JsonArray arr = new();
        if (roomsEnumerable is IEnumerable rooms)
        {
            foreach (object? room in rooms)
            {
                if (room != null)
                {
                    arr.Add(ExtractRoomInfo(room));
                }
            }
        }
        return arr;
    }

    public static JsonObject ExtractRoomInfo(object room)
    {
        return new JsonObject
        {
            ["room_class"] = room.GetType().Name,
            ["room_type"] = GetString(room, "RoomType"),
            ["room_id"] = GetInt(room, "Id"),
            ["model_id"] = FormatModelId(GetMember(room, "ModelId")),
            ["is_pre_finished"] = GetBool(room, "IsPreFinished"),
            ["parent_event_id"] = FormatModelId(GetMember(room, "ParentEventId"))
        };
    }

    private static string BuildCanonicalStateDigestString(JsonObject snapshot)
    {
        StringBuilder sb = new(1024);
        if (snapshot["combat_state"] is JsonObject cs)
        {
            sb.Append("R=").Append(cs["round_number"]?.ToJsonString()).Append(';');
            sb.Append("S=").Append(cs["current_side"]?.ToJsonString()).Append(';');
            if (cs["creatures"] is JsonArray creatures)
            {
                foreach (JsonNode? cNode in creatures)
                {
                    if (cNode is JsonObject c)
                    {
                        sb.Append("C[")
                          .Append(c["combat_id"]?.ToJsonString()).Append(':')
                          .Append(c["model_id"]?.ToJsonString()).Append(':')
                          .Append(c["current_hp"]?.ToJsonString()).Append('/')
                          .Append(c["max_hp"]?.ToJsonString()).Append("+B")
                          .Append(c["block"]?.ToJsonString()).Append(']');
                        if (c["powers"] is JsonArray powers)
                        {
                            foreach (JsonNode? pNode in powers)
                            {
                                if (pNode is JsonObject p)
                                {
                                    sb.Append('(')
                                      .Append(p["id"]?.ToJsonString()).Append('=')
                                      .Append(p["amount"]?.ToJsonString()).Append(')');
                                }
                            }
                        }
                    }
                }
            }
            if (cs["players"] is JsonArray players)
            {
                foreach (JsonNode? pNode in players)
                {
                    if (pNode is JsonObject p)
                    {
                        sb.Append("P[")
                          .Append(p["player_net_id"]?.ToJsonString()).Append(":E=")
                          .Append(p["energy"]?.ToJsonString()).Append(":St=")
                          .Append(p["stars"]?.ToJsonString()).Append(']');
                    }
                }
            }
        }
        else if (snapshot["run_state"] is JsonObject rs)
        {
            sb.Append("Act=").Append(rs["current_act_index"]?.ToJsonString())
              .Append(";Fl=").Append(rs["total_floor"]?.ToJsonString());
        }
        return sb.ToString();
    }
}
