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
}