using System;
using System.Collections;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Reflection;
using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;
using System.Text.Json.Nodes;
using MegaCrit.Sts2.Core.Logging;
using static Sts2StateRecorder.ReflectionAccessor;

namespace Sts2StateRecorder;

/// <summary>
/// Thread-safe append-only NDJSON session writer for Track A full state & action recording.
/// </summary>
internal sealed class RecorderSession : IDisposable
{
    private static readonly JsonWriterOptions NdjsonWriterOptions = new()
    {
        Indented = false,
        Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping
    };

    private readonly object _syncLock = new();
    private readonly string _outputRootDir;
    private StreamWriter? _writer;
    private string? _currentFilePath;
    private string _sessionId;
    private ulong _seq;
    private int _combatIndex;
    private int _combatStepIdx;
    private int _lastHistoryCount;
    private uint? _activeActionId;
    private string? _activeActionClass;

    public string OutputRootDir => _outputRootDir;
    public string? CurrentFilePath => _currentFilePath;

    public RecorderSession(string? customOutputDir = null)
    {
        _outputRootDir = ResolveOutputDirectory(customOutputDir);
        _sessionId = DateTimeOffset.UtcNow.ToString("yyyyMMdd_HHmmss", CultureInfo.InvariantCulture);
        Directory.CreateDirectory(_outputRootDir);
    }

    public static string ResolveOutputDirectory(string? customOutputDir = null)
    {
        if (!string.IsNullOrWhiteSpace(customOutputDir))
        {
            return Path.GetFullPath(customOutputDir);
        }

        string? envDir = Environment.GetEnvironmentVariable("STS2_RECORDER_OUTPUT_DIR");
        if (!string.IsNullOrWhiteSpace(envDir))
        {
            return Path.GetFullPath(envDir);
        }

        // Check for optional recorder_config.json next to Sts2StateRecorder.dll
        try
        {
            string? asmLoc = Assembly.GetExecutingAssembly().Location;
            if (!string.IsNullOrEmpty(asmLoc))
            {
                string? modDir = Path.GetDirectoryName(asmLoc);
                if (!string.IsNullOrEmpty(modDir))
                {
                    string configPath = Path.Combine(modDir, "recorder_config.json");
                    if (File.Exists(configPath))
                    {
                        JsonNode? cfg = JsonNode.Parse(File.ReadAllText(configPath));
                        string? configuredDir = cfg?["output_dir"]?.GetValue<string>();
                        if (!string.IsNullOrWhiteSpace(configuredDir))
                        {
                            return Path.IsPathRooted(configuredDir)
                                ? configuredDir
                                : Path.GetFullPath(Path.Combine(modDir, configuredDir));
                        }
                    }

                    // If located inside <GameRoot>/mods/<ModFolder>, place recordings in <GameRoot>/state_recordings
                    DirectoryInfo? parent = Directory.GetParent(modDir);
                    if (parent != null && string.Equals(parent.Name, "mods", StringComparison.OrdinalIgnoreCase) && parent.Parent != null)
                    {
                        return Path.Combine(parent.Parent.FullName, "state_recordings");
                    }
                }
            }
        }
        catch
        {
            // Fallback to base directory
        }

        return Path.Combine(AppContext.BaseDirectory, "state_recordings");
    }

    public void StartNewRunFile(object? runState)
    {
        lock (_syncLock)
        {
            CloseWriterLocked();

            string timestamp = DateTimeOffset.UtcNow.ToString("yyyyMMdd_HHmmss", CultureInfo.InvariantCulture);
            object? rngSet = GetMember(runState, "Rng");
            string rawSeed = GetString(rngSet, "StringSeed")
                             ?? GetULong(rngSet, "Seed")?.ToString(CultureInfo.InvariantCulture)
                             ?? "unknown_seed";
            string safeSeed = SanitizeFileName(rawSeed);
            _sessionId = $"{timestamp}_{safeSeed}";
            _seq = 0UL;
            _combatIndex = 0;
            _combatStepIdx = 0;
            _lastHistoryCount = 0;
            _activeActionId = null;
            _activeActionClass = null;

            string fileName = $"run_{_sessionId}.full.ndjson";
            _currentFilePath = Path.Combine(_outputRootDir, fileName);
            _writer = new StreamWriter(
                new FileStream(_currentFilePath, FileMode.Create, FileAccess.Write, FileShare.Read),
                new UTF8Encoding(encoderShouldEmitUTF8Identifier: false))
            {
                AutoFlush = true
            };

            Log.Info($"[Sts2StateRecorder] Recording full state & actions to: {_currentFilePath}");
        }
    }

    public void EnsureWriterLocked()
    {
        if (_writer != null)
        {
            return;
        }
        object? runState = StateSnapshotExtractor.GetRunState();
        StartNewRunFile(runState);
    }

    public void OnCombatStarted()
    {
        lock (_syncLock)
        {
            _combatIndex++;
            _combatStepIdx = 0;
            _lastHistoryCount = 0;
        }
    }

    public void SetActiveAction(object? gameAction)
    {
        lock (_syncLock)
        {
            if (gameAction == null)
            {
                _activeActionId = null;
                _activeActionClass = null;
            }
            else
            {
                _activeActionId = GetUInt(gameAction, "Id");
                _activeActionClass = gameAction.GetType().Name;
            }
        }
    }

    /// <summary>
    /// Drains any unrecorded entries from CombatManager.Instance.History and writes each
    /// with its exact step index, active action context, and full state snapshot.
    /// </summary>
    public void DrainPendingCombatHistoryEntries(bool includeStateSnapshotOnEach = true)
    {
        lock (_syncLock)
        {
            object? combatMgr = StateSnapshotExtractor.GetCombatManagerInstance();
            object? history = GetMember(combatMgr, "History");
            if (history == null)
            {
                return;
            }

            object? entriesObj = GetMember(history, "_entries") ?? GetMember(history, "Entries");
            if (entriesObj is not IEnumerable enumerable)
            {
                return;
            }

            List<object> entriesList = new();
            foreach (object? item in enumerable)
            {
                if (item != null)
                {
                    entriesList.Add(item);
                }
            }

            if (entriesList.Count < _lastHistoryCount)
            {
                // CombatHistory was cleared for a new combat
                _lastHistoryCount = 0;
            }

            while (_lastHistoryCount < entriesList.Count)
            {
                int idx = _lastHistoryCount++;
                _combatStepIdx++;
                object entry = entriesList[idx];

                JsonObject payload = new()
                {
                    ["combat_index"] = _combatIndex,
                    ["combat_step_idx"] = _combatStepIdx,
                    ["active_action_id"] = _activeActionId,
                    ["active_action_class"] = _activeActionClass,
                    ["history_entry"] = StateSnapshotExtractor.ExtractCombatHistoryEntry(entry, idx)
                };

                WriteRecordLocked(
                    eventKind: "combat_history_entry",
                    payload: payload,
                    includeFullState: includeStateSnapshotOnEach,
                    includeCanonicalSave: false);
            }
        }
    }

    public void RecordEvent(
        string eventKind,
        JsonObject? payload = null,
        bool includeFullState = true,
        bool includeCanonicalSave = false,
        bool drainHistoryFirst = true)
    {
        lock (_syncLock)
        {
            try
            {
                if (drainHistoryFirst)
                {
                    DrainPendingCombatHistoryEntries(includeStateSnapshotOnEach: true);
                }

                WriteRecordLocked(eventKind, payload, includeFullState, includeCanonicalSave);
            }
            catch (Exception ex)
            {
                Log.Warn($"[Sts2StateRecorder] Failed to record event '{eventKind}': {ex}");
            }
        }
    }

    private void WriteRecordLocked(
        string eventKind,
        JsonObject? payload,
        bool includeFullState,
        bool includeCanonicalSave)
    {
        EnsureWriterLocked();
        if (_writer == null)
        {
            return;
        }

        _seq++;
        JsonObject envelope = new()
        {
            ["schema"] = "sts2_ideal.full_recorder.v1",
            ["session_id"] = _sessionId,
            ["seq"] = _seq,
            ["timestamp_utc"] = DateTimeOffset.UtcNow.ToString("O", CultureInfo.InvariantCulture),
            ["combat_index"] = _combatIndex,
            ["combat_step_idx"] = _combatStepIdx,
            ["active_action_id"] = _activeActionId,
            ["active_action_class"] = _activeActionClass,
            ["event_kind"] = eventKind
        };

        if (payload != null)
        {
            envelope["payload"] = payload;
        }

        if (includeFullState)
        {
            envelope["state_snapshot"] = StateSnapshotExtractor.ExtractFullSnapshot(includeCanonicalSave);
        }

        using MemoryStream ms = new(4096);
        using (Utf8JsonWriter jsonWriter = new(ms, NdjsonWriterOptions))
        {
            envelope.WriteTo(jsonWriter);
        }
        string line = Encoding.UTF8.GetString(ms.GetBuffer(), 0, (int)ms.Length);
        _writer.WriteLine(line);
    }

    private static string SanitizeFileName(string input)
    {
        StringBuilder sb = new(input.Length);
        foreach (char c in input)
        {
            if (char.IsLetterOrDigit(c) || c is '_' or '-')
            {
                sb.Append(c);
            }
            else
            {
                sb.Append('_');
            }
        }
        return sb.Length > 0 ? sb.ToString() : "run";
    }

    private void CloseWriterLocked()
    {
        if (_writer != null)
        {
            try
            {
                _writer.Flush();
                _writer.Dispose();
            }
            catch
            {
                // Ignore close errors
            }
            _writer = null;
        }
    }

    public void Dispose()
    {
        lock (_syncLock)
        {
            CloseWriterLocked();
        }
    }
}
