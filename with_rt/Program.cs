// See https://aka.ms/new-console-template for more information

using System.Runtime.CompilerServices;

namespace with_rt;

using Shared;
using Gurobi;
using System.Linq;
using System;
using System.Diagnostics;

class Program {
    private const int MaxConsToAdd = 5000;

    static IEnumerable<GRBTempConstr> BuildDisjuncts(Problem problem, Chain c1, Chain c2, GRBVar ch, 
        List<GRBVar[]> outerStarts, List<Dictionary<(int, int), GRBVar>> outerEnablers, int upperBound) {
        var (t1, u1, v1t, rt1) = c1;
        var v1succs = new List<int> { -1 };
        if (problem.Trains[t1][v1t].Successors.Count > 0)
            v1succs = problem.Trains[t1][v1t].Successors;
        var u1s = outerStarts[t1][u1];
        var rt1a = Math.Max(1, rt1);

        var (t2, u2, v2t, rt2) = c2;
        var rt2a = Math.Max(1, rt2);
        var v2succs = new List<int> { -1 };
        if (problem.Trains[t2][v2t].Successors.Count > 0)
            v2succs = problem.Trains[t2][v2t].Successors;
        var u2s = outerStarts[t2][u2];

        foreach (var v1 in v1succs) {
            var v1s = v1 < 0 ? u1s + problem.Trains[t1][v1t].MinDuration : outerStarts[t1][v1];
            var en1 = outerEnablers[t1].GetValueOrDefault((v1t, v1), null);
            foreach (var v2 in v2succs) {
                var oei1 = new GRBLinExpr(0);
                if (en1 is not null)
                    oei1 -= upperBound * (1 - en1);

                var v2s = v2 < 0 ? u2s + problem.Trains[t2][v2t].MinDuration : outerStarts[t2][v2];
                var en2 = outerEnablers[t2].GetValueOrDefault((v2t, v2), null);
                var oei2 = new GRBLinExpr(0);
                if (en2 is not null)
                    oei2 -= upperBound * (1 - en2);

                oei1 -= upperBound * (1 - ch);
                oei2 -= upperBound * ch;

                yield return u2s >= v1s + rt1a + oei1;
                yield return u1s >= v2s + rt2a + oei2;
            }
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveOptimization)]
    static (GRBModel model, List<GRBVar[]> outerStarts, List<Dictionary<(int, int), GRBVar>> outerEnablers, GRBVar[], int)
    BuildCpModel(Problem problem, int maxGap) {
        int upperBound = problem.FindUpperBound();
        var distances = problem.FindShortestPaths();

        var env = new GRBEnv();
        env.LogToConsole = 1;
        env.Start();

        var model = new GRBModel(env);
        model.ModelName = problem.Name;
        model.Parameters.IntFeasTol = .47 / upperBound;
        // model.Parameters.IntegralityFocus = 1;

        var outerEnablers = new List<Dictionary<(int, int), GRBVar>>(problem.Trains.Count);
        var outerStarts = new List<GRBVar[]>(problem.Trains.Count);

        for (int t = 0; t < problem.Trains.Count; t++) {
            var train = problem.Trains[t];
            var starts = new GRBVar[train.Count];
            for (int u = 0; u < train.Count; u++) {
                int lb = distances[t][u];
                int ub = train[u].StartUb < 0 ? upperBound : train[u].StartUb;
                starts[u] = model.AddVar(lb, ub, 0, 'I', $"s_{t}_{u}");
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

                var reuse = train[u].Predecessors.Count == 1 && train[u].Successors.Count == 1 &&
                            outerEnablers[t].ContainsKey((train[u].Predecessors[0], u));
                // var reuse = false;
                foreach (var v in train[u].Successors) {
                    int md = train[u].MinDuration;

                    if (needsEnablers >= 0) {
                        // the enablers go with the edges; however, we want to reuse them if possible.
                        var enabler = reuse? outerEnablers[t][(train[u].Predecessors[0], u)] : model.AddVar(0, 1, 0, 'B', $"b_{u}_{v}");
                        // enabler.BranchPriority = 100;
                        outerEnablers[t][(u, v)] = enabler;
                        // if we have a nonzero lower bound, we can't allow that to push all our successors up.
                        // we either go with all zero LB, which seems worse, or we go with big-M here.
                        // but I keep having numerical issues with big-M here.
                        // I can set the IntFeasTol, but I still hit a few issues with it.
                        model.AddConstr(starts[v] >= starts[u] + md * enabler - (1 - enabler) * starts[u].LB, $"aft_{t}_{u}_{v}");
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
                    if (u > 0) {
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
                                successors += 1;
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
        
        

        var heap = new PriorityQueue<(Chain, Chain), int>();

        var bitsNeeded = 0;
        foreach (var chains in tToChains.Values) {
            for (int idx = 0; idx < chains.Count; idx++) {
                var ch1 = chains[idx];
                // common for t1 == v1t but not always
                foreach (var ch2 in chains.Skip(idx + 1)) {
                    if (ch1.Train == ch2.Train)
                        continue;
                    var dis1 = distances[ch1.Train][ch1.Start];
                    var dis2 = distances[ch2.Train][ch2.Start];
                    // var no1to2 = dis1 > 0 && problem.Trains[ch2.Train][ch2.Start].StartUb == 0;
                    // var no2to1 = dis2 > 0 && problem.Trains[ch1.Train][ch1.Start].StartUb == 0;
                    // if (no1to2 && no2to1) {
                    //     continue;
                    // }
                    //
                    // if (no1to2) {
                    //     // successors of 2 must happen before 1 can start
                    //     var rt2 = Math.Max(.1, ch2.ReleaseTime);
                    //     foreach (var v2 in problem.Trains[ch2.Train][ch2.Stop].Successors) {
                    //         model.AddConstr(
                    //             outerStarts[ch1.Train][ch1.Start] >= outerStarts[ch2.Train][v2] + rt2, $"aft_{ch1.Train}_{ch1.Start}_{ch2.Train}_{v2}");
                    //     }
                    //     continue;
                    // }
                    //
                    // if (no2to1) {
                    //     // successors of 1 must happen before 2 can start
                    //     var rt1 = Math.Max(.1, ch1.ReleaseTime);
                    //     foreach (var v1 in problem.Trains[ch1.Train][ch1.Stop].Successors) {
                    //         model.AddConstr(
                    //             outerStarts[ch2.Train][ch2.Start] >= outerStarts[ch1.Train][v1] + rt1, $"aft_{ch2.Train}_{ch2.Start}_{ch1.Train}_{v1}");
                    //     }
                    //     continue;
                    // }

                    heap.Enqueue((ch1, ch2), -Math.Abs(dis1 - dis2));
                    bitsNeeded++;
                }

                while (heap.Count > MaxConsToAdd) {
                    heap.Dequeue();  // yank the largest items
                }
            }
        }
        
        tToChains = null; // for GC
        var bits = model.AddVars(Math.Min(MaxConsToAdd + 5000, bitsNeeded), 'B');
        var bitIndex = 0;
        while (heap.Count > 0) {
            var (ch1, ch2) = heap.Dequeue();
            var conIndex = 0;
            foreach (var con in BuildDisjuncts(problem, ch1, ch2, bits[bitIndex++], outerStarts, outerEnablers, upperBound))
                model.AddConstr(con, $"dis_{bitIndex}_{conIndex++}");
        }

        Console.WriteLine($"Added up to {MaxConsToAdd} of {bitsNeeded} disjunctions.");

        var objectives = new GRBLinExpr(0);
        // var selection = new Random(42).GetItems(problem.Objectives.ToArray(), problem.Objectives.Count / 3);
        var selection = problem.Objectives;
        foreach (var objective in selection) {
            var t = objective.Train;
            var u = objective.Operation;
            var ocv = model.AddVar(0, upperBound, 0, 'I', $"ocv_{t}_{u}");
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
        return (model, outerStarts, outerEnablers, bits, bitIndex);
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

        public VerifyNoOverlapCallback(Problem problem, List<GRBVar[]> outerStarts,
            List<Dictionary<(int, int), GRBVar>> enablers, GRBVar[] disjunctionVars, int disjunctIndex) {
            _problem = problem;
            _outerStarts = outerStarts;
            _outerEnablers = enablers;
            _disjunctionVars = disjunctionVars;
            _disjunctIndex = disjunctIndex;

            Console.CancelKeyPress += (sender, e) => {
                Console.WriteLine("Ctrl+C detected, stopping optimization...");
                Abort();
                e.Cancel = true; // Prevent immediate process termination
            };
        }

        [MethodImpl(MethodImplOptions.AggressiveOptimization)]
        protected override void Callback() {
            if (where == GRB.Callback.MIPSOL) {
                try {
                    // key is res_name, value is start_time, stop_time, train, start_operation, end_operation
                    var resourceIntervals = new Dictionary<string, List<(float, float, int, int, int)>>();
                    for (var t = 0; t < _problem.Trains.Count; t++) {
                        // walk through the path and note the resource intervals.
                        var starts = GetSolution(_outerStarts[t]);
                        var u = 0;
                        while (u + 1 < _problem.Trains[t].Count) {
                            foreach (var v in _problem.Trains[t][u].Successors) {
                                if (!_outerEnablers[t].TryGetValue((u, v), out var enabler) ||
                                    GetSolution(enabler) > 0.5) {
                                    foreach (var r in _problem.Trains[t][u].Resources) {
                                        if (!resourceIntervals.ContainsKey(r.Name))
                                            resourceIntervals[r.Name] = new List<(float, float, int, int, int)>();
                                        resourceIntervals[r.Name].Add(((float)starts[u], (float)starts[v], t, u, v));
                                    }

                                    u = v;
                                    break;
                                }
                            }
                        }
                    }

                    var addedDisjuncts = 0;
                    var usedDisjunctVars = 0;
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
                            var (x1, y1, t1, u1, v1) = pair.Value[rv - 1];
                            var (x2, y2, t2, u2, v2) = pair.Value[rv];
                            if (y1 < x2 || y2 < x1 || t1 == t2)
                                continue; // no overlap
                            // Console.WriteLine(
                            //     $"Needed disjunction for {pair.Key} between {t1}, {u1}, {v1} and {t2}, {u2}, {v2}");
                            var c1 = _problem.FindResourceChain(t1, u1, pair.Key);
                            var c2 = _problem.FindResourceChain(t2, u2, pair.Key);
                            var ub = (int)Math.Max(GetSolution(_outerStarts[t1][^1]), GetSolution(_outerStarts[t2][^1])) + 2;
                            var idx = Interlocked.Increment(ref _disjunctIndex);
                            if (idx >= _disjunctionVars.Length) {
                                throw new InvalidOperationException("Need more disjunction variables.");
                            }

                            usedDisjunctVars++;

                            foreach (var cons in BuildDisjuncts(_problem, c1, c2, _disjunctionVars[idx], _outerStarts,
                                         _outerEnablers, ub)) {
                                addedDisjuncts++;
                                AddLazy(cons);
                            }
                        }
                    }

                    if (addedDisjuncts > 0) {
                        Console.WriteLine($"Added {addedDisjuncts} disjuncts via callback. Used vars: {usedDisjunctVars} ({_disjunctIndex} / {_disjunctionVars.Length}).");
                    }
                }
                catch (Exception e) {
                    Console.WriteLine("Error in callback: " + e);
                }
            }
        }
    }

    static Solution BuildAndOptimize(Problem problem, Stopwatch sw, int maxTime, bool verbose) {
        var (model, outerStarts, outerEnablers, disjunctionVars, disjunctIndex) = BuildCpModel(problem, -1);
        GC.Collect(); // need all the RAM we can get
        model.Parameters.Threads = 8;
        // model.Parameters.Method = 1;
        // model.Parameters.ConcurrentMethod = 3; // don't run Barrier method
        model.Parameters.MemLimit = 32;
        // model.Parameters.Cuts = 0;
        // model.Parameters.Crossover = 1;
        // model.Parameters.Method = 1;
        // model.Parameters.Crossover = 0;
        // model.Parameters.NodeMethod = 1;
        model.Parameters.Heuristics = 0.12;
        model.Parameters.LogToConsole = verbose ? 1 : 0;

        if (disjunctionVars.Length > MaxConsToAdd) {
            model.Parameters.LazyConstraints = 1;
            var cb = new VerifyNoOverlapCallback(problem, outerStarts, outerEnablers, disjunctionVars, disjunctIndex);
            model.SetCallback(cb);
        }
        else {
            model.SetCallback(new TimeoutCallback(30));
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

                var value = (int)Math.Floor((outerStarts[t][u].X + 1e-5));
                solution.Events.Add(new Event { Operation = u, Time = value, Train = t });
            }
        }

        // solution.Events.Sort((a, b) => outerStarts[a.Train][a.Operation].X.CompareTo(outerStarts[b.Train][b.Operation].X));
        // solution.Events.Sort((a, b) => {
        //     if (a.Train == b.Train)  // numeric issues still kill this, so trying to handle a few of those here.
        //         return a.Operation.CompareTo(b.Operation);
        //     
        //     return a.Time.CompareTo(b.Time);
        // });
        
        // Bubble sort implementation with O(n²) complexity
        for (int i = 0; i < solution.Events.Count - 1; i++) {
            for (int j = 0; j < solution.Events.Count - i - 1; j++) {
                var a = solution.Events[j];
                var b = solution.Events[j + 1];
        
                bool shouldSwap = false;
                // if (a.Train == b.Train) {
                //     shouldSwap = a.Operation > b.Operation;
                // } else 
                if (a.Time == b.Time) {
                    // if b releases a resource that a needs, it has to go before it.
                    // find the previous event that was on b.Train:
                    for (int k = j - 1; k >= 0; k--) {
                        if (solution.Events[k].Train == b.Train) {
                            var kop = solution.Events[k].Operation;
                            // check for intersection of resources:
                            shouldSwap = problem.Trains[a.Train][a.Operation].Resources
                                .Any(r => problem.Trains[b.Train][kop].Resources.Contains(r));
                            break;
                        }
                    }
                }
                else {
                    shouldSwap = a.Time > b.Time;
                }
        
                if (shouldSwap) {
                    // Swap elements
                    (solution.Events[j], solution.Events[j + 1]) = (solution.Events[j + 1], solution.Events[j]);
                }
            }
        }
        
        // solution.SquashTimes(problem);
        return solution;
    }

    static void Main(string[] args) {
        var sw = Stopwatch.StartNew();
        // this approach fails because of a faulty assumption:
        // you can repair a failed solution by changing start times.
        // cutting the disjunctions instead makes unnecessary changes.
        // var problemFile = "../../../../../displib_instances_testing/displib_instances_testing/displib_testinstances_headway1.json";
        // var problemFile = "../../../../../displib_instances_phase1/line1_full_7.json";
        // var problemFile = args.Length > 0 ? args[0] : "../../../../../displib_instances_phase1/line1_full_7.json";
        // var problemFile = "../../../../../displib_instances_phase2/line3_8.json";
        // var problemFile = "../../../../../displib_instances_phase1/line1_full_0.json";
        // var problemFile = "../../../../../displib_instances_phase1/line1_critical_3.json";
        // var problemFile = args.Length > 1 ? args[1] : "../../../../../displib_instances_phase2/line8_small_2.json";
        var problemFile = args.Length > 1 ? args[1] : "../../../../../displib_instances_phase2/line4_large_6.json";
        var problem = Problem.LoadFromFile(problemFile);
        Console.WriteLine("Building model for " + problem.Name);
        var solution = BuildAndOptimize(problem, sw, 598, true);
        if (solution != null) {
            var resultFile = $"results/{problem.Name}_solution.json";
            solution.WriteToFile(resultFile);
            Console.WriteLine("Solution found with objective: " + solution.ObjectiveValue);
        }
    }
}