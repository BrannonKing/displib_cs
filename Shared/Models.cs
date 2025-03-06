using System.Text;

namespace Shared;

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Text.Json.Serialization;

public class Resource {
    [JsonPropertyName("resource")] public string Name { get; set; }

    [JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingDefault)]
    public int ReleaseTime { get; set; } = 0;

    public override bool Equals(object obj) => obj is Resource other && Name == other.Name;
    public override int GetHashCode() => Name.GetHashCode();
}

public class Segment {
    public int StartLb { get; set; } = 0;
    public int StartUb { get; set; } = -1;
    public int MinDuration { get; set; } = 0;
    public List<Resource> Resources { get; set; } = new();
    public List<int> Successors { get; set; } = new();
    public List<int> Predecessors { get; set; } = new();
}

public class Objective {
    [JsonPropertyName("type")] public string ObjectiveType { get; set; } = "op_delay";
    public int Train { get; set; }
    public int Operation { get; set; }
    public int Threshold { get; set; } = 0;
    public int Coeff { get; set; } = 0;
    public int Increment { get; set; } = 0;
}

public class Event : IComparable<Event> {
    public int Operation { get; set; }
    public int Time { get; set; }
    public int Train { get; set; }

    public int CompareTo(Event other) => Time.CompareTo(other.Time);
    public override bool Equals(object obj) => obj is Event e && Train == e.Train && Operation == e.Operation;
    public override int GetHashCode() => HashCode.Combine(Train, Operation);
}

public class Problem {
    public List<List<Segment>> Trains { get; set; } = new();

    [JsonPropertyName("objective")] public List<Objective> Objectives { get; set; } = new();

    public string Name { get; set; } = "";

    public int NumTrains => Trains.Count;

    public static Problem LoadFromFile(string filename, bool noWarnings = false) {
        string text = File.ReadAllText(filename);
        var options = new JsonSerializerOptions { PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower };
        var problem = JsonSerializer.Deserialize<Problem>(text, options);
        problem.Name = Path.GetFileNameWithoutExtension(filename);
        problem.BuildPredecessors();
        return problem;
    }

    public void BuildPredecessors() {
        foreach (var train in Trains) {
            for (int i = 0; i < train.Count; i++) {
                foreach (var successor in train[i].Successors) {
                    train[successor].Predecessors.Add(i);
                }
            }
        }
    }

    public Dictionary<string, List<(int, int, int, int)>> FindResourceChains() {
        var result = new Dictionary<string, List<(int, int, int, int)>>();
        for (int t = 0; t < Trains.Count; t++) {
            var train = Trains[t];
            for (int v = 0; v < train.Count; v++) {
                foreach (var resource in train[v].Resources) {
                    int u = FindStartOfChain(train, v, resource.Name);
                    if (!result.ContainsKey(resource.Name)) {
                        result[resource.Name] = new List<(int, int, int, int)>();
                    }

                    result[resource.Name].Add((t, u, v, resource.ReleaseTime));
                }
            }
        }

        return result;
    }

    private static int FindStartOfChain(List<Segment> train, int v, string resourceName) {
        while (v > 0) {
            if (train[v].Predecessors.Count != 1)
                return v;
            var u = train[v].Predecessors[0];
            if (train[u].Resources.All(r => r.Name != resourceName) || train[u].Successors.Count > 1)
                return v;
            v = u;
        }

        return v;
    }

    public int FindUpperBound() {
        var result = 0;
        for (int t = 0; t < Trains.Count; t++) {
            var ub = 0;
            for (int u = 0; u < Trains[t].Count; u++) {
                var segment = Trains[t][u];
                ub = Math.Max(ub, segment.StartLb);
                ub += segment.MinDuration;
                if (segment.Resources.Count > 0) {
                    ub += segment.Resources.Max(sr => sr.ReleaseTime);
                }
            }

            result += ub;
        }

        return result;
    }

    public List<Dictionary<int, int>> FindShortestPaths() {
        var dists = new List<Dictionary<int, int>>();

        for (int t = 0; t < Trains.Count; t++) {
            var train = Trains[t];
            var dist = new Dictionary<int, int> { { 0, 0 } };
            dists.Add(dist);

            for (int u = 0; u < train.Count; u++) {
                var segment = train[u];
                foreach (var v in segment.Successors) {
                    int lb = train[v].StartLb;
                    int toV = Math.Max(dist[u] + segment.MinDuration, lb);
                    if (!dist.ContainsKey(v) || dist[v] > toV) {
                        dist[v] = toV;
                    }
                }
            }
        }

        return dists;
    }
}

public class Solution {
    public List<Event> Events { get; set; } = new();
    public int ObjectiveValue { get; set; }

    public void WriteToFile(string filename) {
        var options = new JsonSerializerOptions
            { WriteIndented = true, PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower };
        string json = JsonSerializer.Serialize(this, options);
        var dir = Path.GetDirectoryName(filename);
        Directory.CreateDirectory(dir);
        File.WriteAllText(filename, json, new UTF8Encoding(false));
    }

    public static Solution LoadFromFile(string filename) {
        string text = File.ReadAllText(filename);
        var options = new JsonSerializerOptions { PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower };
        return JsonSerializer.Deserialize<Solution>(text, options)!;
    }

    public static int FindScore(Problem problem, List<Event> events, bool fallback = false) {
        var score = 0;

        foreach (var objective in problem.Objectives) {
            int t = objective.Train;
            int op = objective.Operation;
            var threshold = objective.Threshold;

            // Filter events for the specific train and operation
            var opEvents = events.Where(e => e.Operation == op && e.Train == t).ToList();

            if (opEvents.Count == 0) {
                if (!fallback) {
                    continue;
                }

                // Fallback: filter events for the specific train only
                opEvents = events.Where(e => e.Train == t).ToList();
                if (opEvents.Count == 0) {
                    continue;
                }
                threshold = 0; // Reset threshold for fallback
            }

            // Get the last event in the filtered list
            var ev = opEvents.Last();

            // Calculate score
            score += objective.Coeff * Math.Max(0, ev.Time - threshold);
            score += objective.Increment * (ev.Time >= threshold ? 1 : 0);
        }

        return score;
    }

    public void SquashTimes(Problem problem) {
        var result = new List<Event>();
        var tips = new int[problem.Trains.Count];
        for (int i = 0; i < tips.Length; i++)
            tips[i] = -1;

        var held = new Dictionary<string, int>();
        var releases = new Dictionary<string, (int, int)>();

        foreach (var e in this.Events) {
            int t = e.Train;
            int u = e.Operation;

            var prevTStart = 0;
            if (tips[t] >= 0) {
                var prevTSeg = problem.Trains[t][result[tips[t]].Operation];
                prevTStart = result[tips[t]].Time + prevTSeg.MinDuration;
            }

            var releaseTime = 0;
            var seg = problem.Trains[t][u];
            foreach (var resource in seg.Resources) {
                if (held.TryGetValue(resource.Name, out int heldTrain) && heldTrain != t) {
                    throw new InvalidOperationException("Resource is not available!");
                }

                if (releases.TryGetValue(resource.Name, out var releaseInfo)) {
                    var t2 = releaseInfo.Item1;
                    var rt = releaseInfo.Item2;
                    if (t2 != t) {
                        releaseTime = Math.Max(releaseTime, rt);
                    }
                }
            }

            var prevStart = result.Count > 0 ? result[^1].Time : 0;
            var time = Math.Max(Math.Max(prevStart, prevTStart), Math.Max(seg.StartLb, releaseTime));

            if (tips[t] >= 0) {
                var prevTSeg = problem.Trains[t][result[tips[t]].Operation];
                foreach (var resource in prevTSeg.Resources) {
                    held.Remove(resource.Name);
                    if (resource.ReleaseTime > 0) {
                        releases[resource.Name] = (t, resource.ReleaseTime + time);
                    }
                }
            }

            tips[t] = result.Count;
            result.Add(new Event { Train = t, Operation = u, Time = time });

            foreach (var resource in seg.Resources) {
                held[resource.Name] = t;
            }

            releases = releases
                .Where(kvp => kvp.Value.Item2 > time)
                .ToDictionary(kvp => kvp.Key, kvp => kvp.Value);
        }

        this.Events = result;
        this.ObjectiveValue = FindScore(problem, result);
    }
}