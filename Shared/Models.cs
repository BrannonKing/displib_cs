using MathNet.Numerics.LinearAlgebra.Double;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;

namespace Shared;

public class Resource {
    [JsonPropertyName("resource")] public string Name { get; set; }

    [JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingDefault)]
    public int ReleaseTime { get; set; } = 0;

    public override bool Equals(object obj) => obj is Resource other && Name == other.Name;
    public override int GetHashCode() => Name.GetHashCode();

    public override string ToString() {
        return $"Resource: {Name} ({ReleaseTime})";
    }
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
    public int Operation { get; init; }
    public int Time { get; set; }
    public int Train { get; init; }

    public int CompareTo(Event other) => Time.CompareTo(other.Time);
    public override bool Equals(object obj) => obj is Event e && Train == e.Train && Operation == e.Operation;
    public override int GetHashCode() => HashCode.Combine(Train, Operation);
}

public record Chain(int Train, int Start, int Stop, int ReleaseTime);

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

    public Chain FindResourceChain(int t, int v, string name) {
        var train = Trains[t];
        while (train[v].Successors.Count == 1 && train[train[v].Successors[0]].Predecessors.Count == 1 &&
               train[train[v].Successors[0]].Resources.Any(r => r.Name == name))
            v = train[v].Successors[0];
        int u = FindStartOfChain(train, v, name);
        return new Chain(t, u, v, train[v].Resources.First(x => x.Name == name).ReleaseTime);
    }

    public Dictionary<string, List<Chain>> FindResourceChains() {
        var result = new Dictionary<string, List<Chain>>();
        for (int t = 0; t < Trains.Count; t++) {
            var train = Trains[t];
            for (int v = 0; v < train.Count; v++) {
                foreach (var resource in train[v].Resources) {
                    int u = FindStartOfChain(train, v, resource.Name);
                    if (!result.TryGetValue(resource.Name, out var value)) {
                        result[resource.Name] = [
                            new Chain(t, u, v, resource.ReleaseTime)
                        ];
                        continue;
                    }

                    var last = value[^1];
                    if (last.Train == t && last.Start == u) {
                        result[resource.Name][^1] = new Chain(t, u, v, resource.ReleaseTime);
                    }
                    else
                        result[resource.Name].Add(new Chain(t, u, v, resource.ReleaseTime));
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

    private const double NegInf = -1e10;

    /// <summary>
    /// Computes the Max-Plus product of two matrices A and B.
    /// </summary>
    /// <param name="A">First input matrix</param>
    /// <param name="B">Second input matrix</param>
    /// <returns>The Max-Plus product matrix</returns>
    public static SparseMatrix MaxPlusMultiply(SparseMatrix A, SparseMatrix B) {
        int n = A.RowCount;
        if (A.ColumnCount != B.RowCount || A.RowCount != B.ColumnCount)
            throw new ArgumentException("Matrix dimensions must be compatible for multiplication");

        // Initialize result as a sparse matrix (unstored elements are 0, interpreted as -∞)
        var C = SparseMatrix.Create(n, n, 0.0);

        // Dictionary to accumulate maximum values before setting in sparse matrix
        var maxValues = new Dictionary<(int i, int j), double>();

        // Iterate over non-zero elements in A
        foreach (var (i, k, a_ik) in A.Storage.EnumerateNonZeroIndexed())
        {
            // Iterate over non-zero elements in B for column k
            foreach (var (k2, j, b_kj) in B.Storage.EnumerateNonZeroIndexed())
            {
                if (k2 != k || b_kj <= 0) continue; // Match k and skip -∞

                double sum = a_ik + b_kj;
                if (sum <= 0) continue; // Skip if sum is -∞

                var key = (i, j);
                if (maxValues.TryGetValue(key, out double currentMax))
                {
                    maxValues[key] = Math.Max(currentMax, sum);
                }
                else
                {
                    maxValues[key] = sum;
                }
            }
        }

        // Set the computed maximums in the sparse matrix
        foreach (var kvp in maxValues)
        {
            C.At(kvp.Key.i, kvp.Key.j, kvp.Value);
        }

        return C;
    }

    /// <summary>
    /// Computes A to the power of k under Max-Plus algebra using binary exponentiation.
    /// </summary>
    /// <param name="A">Base matrix</param>
    /// <param name="k">Non-negative exponent</param>
    /// <returns>The matrix A raised to the power k in Max-Plus algebra</returns>
    public static SparseMatrix MaxPlusPower(SparseMatrix A, int k) {
        int n = A.RowCount;
        var result = SparseMatrix.Create(n, n, NegInf);
        for (var i = 0; i < n; ++i)
            result.At(i, i, 0.0);
        
        var baseMatrix = A;
        while (k > 0) {
            Console.WriteLine("Start: " + k);
            if (k % 2 == 1) {
                result = MaxPlusMultiply(result, baseMatrix);
            }

            baseMatrix = MaxPlusMultiply(baseMatrix, baseMatrix);
            k /= 2;
        }

        return result;
    }
    
    public SparseMatrix BuildGraph(int minRt = 1)
    {
        // Number of segments
        var n = Trains.Sum(t => t.Count);

        // Mapping from segment index to (train index, segment index within train)
        var segToTu = new List<(int t, int u)>();
        for (var t = 0; t < Trains.Count; t++)
        {
            var train = Trains[t];
            for (var u = 0; u < train.Count; u++)
            {
                segToTu.Add((t, u));
            }
        }

        // Reverse mapping from (t, u) to segment index
        var tuToSeg = segToTu.Select((tup, i) => new { tup, i })
                             .ToDictionary(x => x.tup, x => x.i);

        // Initialize adjacency matrix with zeros
        var A = new SparseMatrix(n, n);

        // Add edges for train segments
        for (int t = 0; t < Trains.Count; t++)
        {
            var train = Trains[t];
            for (int u = 0; u < train.Count; u++)
            {
                var segment = train[u];
                int useg = tuToSeg[(t, u)];
                foreach (int v in segment.Successors)
                {
                    int vseg = tuToSeg[(t, v)];
                    A[useg, vseg] = segment.MinDuration;
                }
            }
        }

        // Add edges for resource constraints
        var tToChains = FindResourceChains();
        Console.WriteLine($"   Found {tToChains.Count} separate resources");

        foreach (var pair in tToChains)
        {
            string name = pair.Key;
            var chains = pair.Value;
            for (int i = 0; i < chains.Count; i++)
            {
                var (t1, u1, v1t, rt1) = chains[i];
                for (int j = i + 1; j < chains.Count; j++)
                {
                    var (t2, u2, v2t, rt2) = chains[j];
                    if (t1 == t2)
                    {
                        continue;
                    }

                    var v1Succs = Trains[t1][v1t].Successors;
                    var v2Succs = Trains[t2][v2t].Successors;
                    int u1seg = tuToSeg[(t1, u1)];
                    int u2seg = tuToSeg[(t2, u2)];

                    // Edges from v1's successors to u2
                    foreach (int v1 in v1Succs)
                    {
                        int v1seg = tuToSeg[(t1, v1)];
                        A[v1seg, u2seg] = Math.Max(A[v1seg, u2seg], Math.Max(minRt, rt1));
                    }

                    // Edges from v2's successors to u1
                    foreach (int v2 in v2Succs)
                    {
                        int v2seg = tuToSeg[(t2, v2)];
                        A[v2seg, u1seg] = Math.Max(A[v2seg, u1seg], Math.Max(minRt, rt2));
                    }
                }
            }
        }

        return A;
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
            var ev = events.LastOrDefault(e => e.Operation == op && e.Train == t);

            if (ev == null) {
                continue;
            }

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