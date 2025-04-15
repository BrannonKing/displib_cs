// See https://aka.ms/new-console-template for more information

using System.Runtime.CompilerServices;

namespace with_rt;

using Shared;
using Gurobi;
using System.Linq;
using System;
using System.Diagnostics;

class Program {
    private const int MaxConsToAdd = 25000;
    private const int MaxBitsForCons = 40000;

    static IEnumerable<GRBTempConstr> BuildDisjuncts(Problem problem, Chain c1, Chain c2, GRBVar ch, 
        List<GRBVar[]> outerStarts, List<Dictionary<(int, int), GRBVar>> outerEnablers, double upperBound, string name) {
        var (t1, u1, v1t, rt1) = c1;
        var v1succs = problem.Trains[t1][v1t].Successors;
        var u1s = outerStarts[t1][u1];
        var rt1a = Math.Max(0.1, rt1);

        var (t2, u2, v2t, rt2) = c2;
        var v2succs = problem.Trains[t2][v2t].Successors;
        if (v1succs.Count + v2succs.Count == 0)
            yield break; // no successors, no disjunctions
        
        var rt2a = Math.Max(0.1, rt2);
        var u2s = outerStarts[t2][u2];

        foreach (var v1 in v1succs) { // u2 happens after all v1's successors
            // if (problem.Trains[t1][v1].Resources.Any(r => r.Name == name))
            //     throw new InvalidOperationException("v1 should not have resource " + name);
            
            var v1s = outerStarts[t1][v1];
            var en1 = outerEnablers[t1].GetValueOrDefault((v1t, v1), null);
            var oei1 = new GRBLinExpr(0);
            if (en1 is not null)
                oei1 -= upperBound * (1 - en1);
            oei1 -= upperBound * (1 - ch);
            yield return u2s >= v1s + rt1a + oei1;
        }

        foreach (var v2 in v2succs) {
            // if (problem.Trains[t2][v2].Resources.Any(r => r.Name == name))
            //     throw new InvalidOperationException("v1 should not have resource " + name);

            var v2s = outerStarts[t2][v2];
            var en2 = outerEnablers[t2].GetValueOrDefault((v2t, v2), null);
            var oei2 = new GRBLinExpr(0);
            if (en2 is not null)
                oei2 -= upperBound * (1 - en2);
            oei2 -= upperBound * ch;
            yield return u1s >= v2s + rt2a + oei2;
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveOptimization)]
    static (GRBModel model, List<GRBVar[]> outerStarts, List<Dictionary<(int, int), GRBVar>> outerEnablers, GRBVar[], int, int)
    BuildCpModel(Problem problem, int maxGap) {
        int upperBound = problem.FindUpperBound();
        var distances = problem.FindShortestPaths();

        var env = new GRBEnv();
        env.LogToConsole = 1;
        env.Start();

        var model = new GRBModel(env);
        model.ModelName = problem.Name;
        model.Parameters.IntFeasTol = .47 / upperBound;
        // model.Parameters.FeasibilityTol = .47 / upperBound; 

        var outerEnablers = new List<Dictionary<(int, int), GRBVar>>(problem.Trains.Count);
        var outerStarts = new List<GRBVar[]>(problem.Trains.Count);

        for (int t = 0; t < problem.Trains.Count; t++) {
            var train = problem.Trains[t];
            var starts = new GRBVar[train.Count];
            for (int u = 0; u < train.Count; u++) {
                var lb = distances[t][u];
                var ub = train[u].StartUb < 0 ? upperBound : train[u].StartUb;
                starts[u] = model.AddVar(lb, ub, 0, 'C', $"s_{t}_{u}");
                // starts[u].Start = distances[t][u];
            }
            model.Update();

            outerStarts.Add(starts);
            outerEnablers.Add(new Dictionary<(int, int), GRBVar>());

            var needsEnablers = -1;
            for (int u = 0; u < train.Count; u++) {
                if (needsEnablers < 0 && train[u].Successors.Count > 1) {
                    needsEnablers = u;
                }

                foreach (var v in train[u].Successors) {
                    var md = train[u].MinDuration;

                    if (needsEnablers >= 0) {
                        var enabler = model.AddVar(0, 1, 0, 'B', $"b_{u}_{v}");
                        enabler.BranchPriority = 100;
                        outerEnablers[t][(u, v)] = enabler;
                        // if we have a nonzero lower bound, we can't allow that to push all our successors up.
                        // we either go with all zero LB, which seems worse, or we go with big-M here.
                        // but I keep having numerical issues with big-M here.
                        // I can set the IntFeasTol, but I still hit a few issues with it.
                        // if (starts[u].LB > 50000) {
                        //     model.AddGenConstrIndicator(enabler, 1, starts[v] >= starts[u] + md, $"aft_{t}_{u}_{v}");
                        // }
                        // else 
                        {
                            var mlb = Math.Max(starts[v].LB, starts[u].LB); // could use upperBound
                            model.AddConstr(starts[v] >= starts[u] + md * enabler - (1 - enabler) * mlb,
                                $"aft_{t}_{u}_{v}");
                        }
                        // model.AddGenConstrIndicator(enabler, 1, starts[v] >= starts[u] + md, $"aft_{t}_{u}_{v}");
                    }
                    else {
                        model.AddConstr(starts[v] >= starts[u] + md, $"aft_{t}_{u}_{v}");
                    }
                }
            }

            if (needsEnablers >= 0) {
                for (var u = needsEnablers; u < train.Count; u++) {
                    var predecessors = new GRBLinExpr(0);
                    if (u > needsEnablers) {
                        foreach (var p in train[u].Predecessors) {
                            if (outerEnablers[t].TryGetValue((p, u), out var en))
                                predecessors += en;
                            else
                                predecessors += 1;
                        }

                        if (train[u].Predecessors.Count > 1) {
                            model.AddConstr(predecessors <= 1, $"p_{t}_{u}");
                        }
                    }
                    else {
                        predecessors += 1;
                    }

                    var successors = new GRBLinExpr(0);
                    if (u + 1 < train.Count) {
                        foreach (var s in train[u].Successors) {
                            if (outerEnablers[t].TryGetValue((u, s), out var en))
                                successors += en;
                            else
                                throw new InvalidOperationException("Unexpected");
                        }

                        if (train[u].Successors.Count > 1) {
                            model.AddConstr(successors <= 1, $"s_{t}_{u}");
                        }
                    }
                    else {
                        successors += 1;
                    }

                    model.AddConstr(predecessors == successors, $"ps_{t}_{u}");
                }
            }
        }

        var tToChains = problem.FindResourceChains();
        
        // we're gonna change this:
        // 1. loop through all options and add bin variables for each combo.
        // 2. store the gaps along with the combo in a heap.
        // 3. so that we keep the smallest items.
        // 4. we need a new function to generate the actual constraints.
        var heap = new PriorityQueue<(Chain, Chain, string), int>();

        var bitsNeeded = 0;
        foreach (var (name, chains) in tToChains) {
            for (int idx = 0; idx < chains.Count; idx++) {
                var ch1 = chains[idx];
                // common for t1 == v1t but not always
                foreach (var ch2 in chains.Skip(idx + 1)) {
                    if (ch1.Train == ch2.Train)
                        continue;
                    var dis1 = distances[ch1.Train][ch1.Start];
                    var dis2 = distances[ch2.Train][ch2.Start];
                    heap.Enqueue((ch1, ch2, name), -Math.Abs(dis1 - dis2));
                    bitsNeeded++;
                }

                while (heap.Count > MaxConsToAdd) {
                    heap.Dequeue();  // yank the largest items
                }
            }
        }
        
        tToChains = null; // for GC
        var bits = model.AddVars(Math.Min(MaxBitsForCons, bitsNeeded), 'B');
        var bitIndex = 0;
        while (heap.Count > 0) {
            var (ch1, ch2, name) = heap.Dequeue();
            var conIndex = 0;
            foreach (var con in BuildDisjuncts(problem, ch1, ch2, bits[bitIndex++], outerStarts, outerEnablers, upperBound, name))
                model.AddConstr(con, $"dis_{bitIndex}_{conIndex++}");
        }

        Console.WriteLine($"Added up to {MaxConsToAdd} of {bitsNeeded} disjunctions.");

        var objectives = new GRBLinExpr(0);
        foreach (var objective in problem.Objectives) {
            var t = objective.Train;
            var u = objective.Operation;
            var ocv = model.AddVar(0, upperBound, 0, 'C', $"ocv_{t}_{u}");
            var ocb = model.AddVar(0, 1, 0, 'B', $"ocb_{t}_{u}");
            model.AddConstr(ocv >= outerStarts[t][u] - objective.Threshold - upperBound * (1 - ocb), $"obj_{t}_{u}");
            var enables = new GRBLinExpr(0);
            var found = 0;
            foreach (var p in problem.Trains[t][u].Predecessors)
                if (outerEnablers[t].TryGetValue((p, u), out var en)) {
                    enables += en;
                    found++;
                }

            model.AddConstr(ocb >= enables + problem.Trains[t][u].Predecessors.Count - found, $"ob2_{t}_{u}");
            objectives += objective.Coeff * ocv + objective.Increment * ocb;
        }

        model.SetObjective(objectives, GRB.MINIMIZE);
        return (model, outerStarts, outerEnablers, bits, bitIndex, upperBound);
    }

    class TimeoutCallback : GRBCallback {
        private readonly int _seconds;
        private readonly Stopwatch _watch = new Stopwatch();

        public TimeoutCallback(int seconds) {
            _seconds = seconds;

            Console.CancelKeyPress += (sender, e) => {
                Console.WriteLine("Ctrl+C detected, stopping optimization...");
                Abort();
                e.Cancel = true; // Prevent immediate process termination
            };
        }

        protected override void Callback() {
            if (where == GRB.Callback.MIPSOL) {
                _watch.Restart();
            }

            if (_watch.IsRunning && _watch.Elapsed.TotalSeconds >= _seconds) {
                Abort();
            }
        }
    }

    class VerifyNoOverlapCallback : GRBCallback {
        private readonly List<GRBVar[]> _outerStarts;
        private readonly List<Dictionary<(int, int), GRBVar>> _outerEnablers;
        private readonly GRBVar[] _disjunctionVars;
        private readonly Problem _problem;
        private int _disjunctIndex;
        private double _upperBound; 

        public VerifyNoOverlapCallback(Problem problem, List<GRBVar[]> outerStarts,
            List<Dictionary<(int, int), GRBVar>> enablers, GRBVar[] disjunctionVars, int disjunctIndex,
            double upperBound) {
            _problem = problem;
            _outerStarts = outerStarts;
            _outerEnablers = enablers;
            _disjunctionVars = disjunctionVars;
            _disjunctIndex = disjunctIndex;
            _upperBound = upperBound;

            Console.CancelKeyPress += (sender, e) => {
                Console.WriteLine("Ctrl+C detected, stopping optimization...");
                Abort();
                e.Cancel = true; // Prevent immediate process termination
            };
        }

        [MethodImpl(MethodImplOptions.AggressiveOptimization)]
        protected override void Callback() {
            if (where == GRB.Callback.MIPSOL) {
                double newUpperBound = 0;
                try {
                    // key is res_name, value is start_time, stop_time, train, start_operation, end_operation
                    var resourceIntervals = new Dictionary<string, List<(float, float, int, int, int, int)>>();
                    for (var t = 0; t < _problem.Trains.Count; t++) {
                        // walk through the path and note the resource intervals.
                        var starts = GetSolution(_outerStarts[t]);
                        newUpperBound = Math.Max(newUpperBound, starts[^1]);
                        var u = 0;
                        while (u + 1 < _problem.Trains[t].Count) {
                            foreach (var v in _problem.Trains[t][u].Successors) {
                                if (!_outerEnablers[t].TryGetValue((u, v), out var enabler) ||
                                    GetSolution(enabler) > 0.5) {
                                    foreach (var r in _problem.Trains[t][u].Resources) {
                                        if (!resourceIntervals.ContainsKey(r.Name))
                                            resourceIntervals[r.Name] = new List<(float, float, int, int, int, int)>();
                                        resourceIntervals[r.Name].Add(((float)starts[u], (float)starts[v], t, u, v, r.ReleaseTime));
                                    }

                                    u = v;
                                    break;
                                }
                            }
                        }
                    }

                    var addedDisjuncts = 0;
                    // sort the resource intervals, then check them for overlap.
                    foreach (var pair in resourceIntervals) {
                        pair.Value.Sort((a, b) => {
                            var ab = a.Item1.CompareTo(b.Item1);
                            if (ab == 0)
                                ab = a.Item2.CompareTo(b.Item2);
                            return ab;
                        });
                        // for each overlap, lookup the right disjunctions on it and add them as lazy constraints:
                        for (var rv = 1; rv < pair.Value.Count; rv++) {
                            var (x1, y1, t1, u1, v1, rt1) = pair.Value[rv - 1];
                            var (x2, y2, t2, u2, v2, rt2) = pair.Value[rv];
                            // x1 <= x2 via sort
                            
                            if (y1 + Math.Max(0, rt1) - 1e-6 <= x2 || y2 + Math.Max(0, rt2) - 1e-6 <= x1 || t1 == t2)
                                continue; // no overlap
                            // Console.WriteLine(
                            //     $"Needed disjunction for {pair.Key} between {t1}, {u1}, {v1} and {t2}, {u2}, {v2}");
                            var c1 = _problem.FindResourceChain(t1, u1, pair.Key);
                            var c2 = _problem.FindResourceChain(t2, u2, pair.Key);
                            var idx = Interlocked.Increment(ref _disjunctIndex);
                            if (idx >= _disjunctionVars.Length) {
                                Console.WriteLine("ERROR: Out of bits!");
                                throw new InvalidOperationException("Need to reserve more bit vars.");
                            }

                            var ub = _upperBound; // Math.Max(GetSolution(_outerStarts[t1][^1]), GetSolution(_outerStarts[t2][^1])) + 1;
                            foreach (var cons in BuildDisjuncts(_problem, c1, c2, _disjunctionVars[idx], _outerStarts,
                                         _outerEnablers, ub, pair.Key)) {
                                addedDisjuncts++;
                                AddLazy(cons);
                            }
                        }
                    }

                    if (addedDisjuncts > 0) {
                        Console.WriteLine($"Added {addedDisjuncts} disjuncts via callback.");
                    }
                    else {
                        _upperBound = newUpperBound;
                        Console.WriteLine($"Upper Bound updated to {newUpperBound}");
                    }
                }
                catch (Exception e) {
                    Console.WriteLine("Error in callback: " + e);
                }
            }
            else if (where == GRB.Callback.MIPNODE && GetIntInfo(GRB.Callback.MIPNODE_STATUS) == GRB.Status.OPTIMAL) {

                // chance to try to find a greedy solution:
                if (Random.Shared.NextSingle() < 0.8) {
                    return;
                }

                for (var t = 0; t < _problem.Trains.Count; t++) {
                    var enablers = GetSolution(_outerEnablers[t].Values.ToArray());
                    foreach (var enable in enablers) {
                        if (enable is > .25 and < 0.75) {
                            return;  // require that all enablers are decided (but not all disjunctives)
                        }
                    }
                }
            
                // build a graph with the chosen paths. Then complete the disjunctions for it.
                var nodeG = _baseGraph.Clone();
                var needDecision = new List<(Edge, Edge)>();
                foreach (var ((u, v), (index, disjunctive)) in _choices) {
                    if (nodeValues[index] is <= .25 or >= 0.75) {  // aka, it's decided
                        if (disjunctive) {
                            if (nodeValues[index] <= 0.25) {
                                var (farU, farV) = _disjunctPairs[(u, v)];
                                nodeG.AddEdge(farU, farV);
                            }
                            else {
                                nodeG.AddEdge(u, v);
                            }
                        }
                        else if (nodeValues[index] >= 0.75) {
                            nodeG.AddEdge(u, v);
                        }
                    }
                    else if (disjunctive) {
                        var (farU, farV) = _disjunctPairs[(u, v)];
                        needDecision.Add((new Edge(u, v), new Edge(farU, farV)));
                    }
                }

                var noCycles = nodeG.AddReversibleEdgesWithBacktracking(needDecision);
                if (noCycles) {
                    for (int i = 0; i < nodeValues.Length; i++) {
                        nodeValues[i] = Math.Round(nodeValues[i]);
                    }

                    foreach (var (edge1, edge2) in needDecision) {
                        var wants2nd = nodeG.HasEdge(edge2.U, edge2.V);
                        var (index, disj) = _choices[(edge1.U, edge1.V)];
                        Debug.Assert(disj);
                        nodeValues[index] = wants2nd ? 0.0 : 1.0;
                    }
                
                    // var score = 1000000000; 
                    // var success = BurnDown(nodeG, score, nodeValues);
                    // if (success) {
                    //     SetSolution(_allVariables, nodeValues);
                    //     var objective2 = UseSolution();
                    //     if (objective2 < GRB.INFINITY) {
                    //         Console.WriteLine("We found one burnt! Objective: " + objective2);
                    //     }
                    // }
                
                    SetSolution(_allVariables, nodeValues);
                    var objective = UseSolution();
                    if (objective < GRB.INFINITY) {
                        Console.WriteLine("We found one on a MIP node! Objective: " + objective);
                    }
                }

            }
        }
    }

    static Solution BuildAndOptimize(Problem problem, Stopwatch sw, int maxTime, bool verbose) {
        var (model, outerStarts, outerEnablers, disjunctionVars, disjunctIndex, upperBound) = BuildCpModel(problem, -1);
        GC.Collect(); // need all the RAM we can get
        model.Parameters.Threads = 8;
        // model.Parameters.MIPFocus = 1;
        // model.Parameters.Heuristics = 0.1;
        // model.Parameters.Method = 1;
        // model.Parameters.ConcurrentMethod = 3; // don't run Barrier method
        model.Parameters.MemLimit = 32;
        // model.Parameters.Cuts = 0;
        // model.Parameters.Crossover = 1;
        // model.Parameters.Method = 1;
        // model.Parameters.Crossover = 0;
        model.Parameters.LogToConsole = verbose ? 1 : 0;

        if (disjunctionVars.Length > MaxConsToAdd) {
            model.Parameters.LazyConstraints = 1;
            var cb = new VerifyNoOverlapCallback(problem, outerStarts, outerEnablers, disjunctionVars, disjunctIndex, upperBound);
            model.SetCallback(cb);
        }
        else {
            model.SetCallback(new TimeoutCallback(300));
        }

        model.Parameters.TimeLimit = maxTime - Math.Ceiling(sw.Elapsed.TotalSeconds);
        try {
            model.Optimize();

            if (model.SolCount > 0) {
                return ExtractSolution(((GRBLinExpr)model.GetObjective()).Value, problem, outerStarts, outerEnablers);
            }
        }
        finally {
            var env = model.GetEnv();
            model.Dispose();
            env.Dispose();
        }

        return null;
    }

    private static Solution ExtractSolution(double objectiveValue, Problem problem, List<GRBVar[]> outerStarts,
        List<Dictionary<(int, int), GRBVar>> outerEnablers) {
        var solution = new Solution {
            ObjectiveValue = (int)Math.Floor(objectiveValue + 1e-5)
        };
        
        var actualTimes = new Dictionary<(int, int), double>();

        for (var t = 0; t < problem.Trains.Count; t++) {
            for (var u = 0; u < problem.Trains[t].Count; u++) {
                if (u > 0) {
                    var enables = 0.0;
                    foreach (var p in problem.Trains[t][u].Predecessors) {
                        if (outerEnablers[t].ContainsKey((p, u))) {
                            enables += outerEnablers[t][(p, u)].X;
                        }
                        else {
                            enables += 1;
                            break;
                        }
                    }

                    if (enables < 0.5)
                        continue;
                }

                actualTimes[(t, u)] = Math.Round(outerStarts[t][u].X, 5); // assuming 1e-5 tolerance
                var value = (int)Math.Floor((outerStarts[t][u].X + 1e-5));
                solution.Events.Add(new Event { Operation = u, Time = value, Train = t });
            }
        }
        
        // have to ensure that ties are handled correctly, which won't happen with List.Sort:
        BubbleSort(actualTimes, solution.Events);
        
        solution.SquashTimes(problem);
        return solution;
    }
    
    static void BubbleSort(Dictionary<(int, int), double> actualTimes, List<Event> events) {
        int n = events.Count;
        for (int i = 0; i < n - 1; i++) {
            for (int j = 0; j < n - i - 1; j++) {
                var a = events[j];
                var b = events[j + 1];

                var (at, bt) = (actualTimes[(a.Train, a.Operation)], actualTimes[(b.Train, b.Operation)]); 
                if (at > bt) {
                    (events[j], events[j + 1]) = (events[j + 1], events[j]);
                } else if (at == bt) {
                    if (a.Train == b.Train && a.Operation > b.Operation) {
                        (events[j], events[j + 1]) = (events[j + 1], events[j]);
                    }
                }
            }
        }
    }
    
    static void Main(string[] args) {
        var sw = Stopwatch.StartNew();
        // this approach fails because of a faulty assumption:
        // you can repair a failed solution by changing start times.
        // cutting the disjunctions instead makes unnecessary changes.
        // var problemFile = "../../../../../displib_instances_testing/displib_instances_testing/displib_testinstances_swapping2.json";
        var problemFile = "../../../../../displib_instances_phase1/line1_critical_9.json";
        // var problemFile = args.Length > 0 ? args[0] : "../../../../../displib_instances_phase1/line3_3.json";
        // var problemFile = "../../../../../displib_instances_phase2/line3_8.json";
        // var problemFile = "../../../../../displib_instances_phase1/line1_full_0.json";
        // var problemFile = "../../../../../displib_instances_phase1/line2_headway_8.json";
        // var problemFile = args.Length > 1 ? args[1] : "../../../../../displib_instances_phase2/line4_large_1.json";
        var problem = Problem.LoadFromFile(problemFile);
        Console.WriteLine("Building model for " + problem.Name);

        var A = problem.BuildGraph();
        var B = Problem.MaxPlusPower(A, A.ColumnCount - 1);
        Console.WriteLine("MaxPlusPower: " + B.Storage.Enumerate().Max());

        // var solution = BuildAndOptimize(problem, sw, 598, true);
        // if (solution != null) {
        //     var resultFile = $"results/{problem.Name}_solution.json";
        //     solution.WriteToFile(resultFile);
        //     Console.WriteLine("Solution found with objective: " + solution.ObjectiveValue);
        // }
    }
}