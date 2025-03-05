// See https://aka.ms/new-console-template for more information

using System.Diagnostics;
using System.Runtime.CompilerServices;

namespace with_rt;

using Shared;
using Gurobi;
using System.Linq;
using System;
using TqdmSharp;

class Program {
    [MethodImpl(MethodImplOptions.AggressiveOptimization)]
    static (GRBModel model, List<List<GRBVar>> outerStarts, List<Dictionary<(int, int), GRBVar>> outerEnablers,
        Dictionary<(int, int, int, int, int, int), (int, GRBTempConstr, GRBTempConstr, string)>)
    BuildCpModel(Problem problem, int maxGap) {
        int upperBound = problem.FindUpperBound();
        var distances = problem.FindShortestPaths();

        var env = new GRBEnv();
        env.LogToConsole = 1;
        env.Start();

        var model = new GRBModel(env);
        model.ModelName = problem.Name;

        var outerEnablers = new List<Dictionary<(int, int), GRBVar>>();
        var outerStarts = new List<List<GRBVar>>();

        var tq1 = new Tqdm.ProgressBar(total: problem.Trains.Count, printsPerSecond: 4);
        tq1.SetLabel("Vars and Cons for segments");
        for (int t = 0; t < problem.Trains.Count; t++) {
            tq1.Progress(t);
            var train = problem.Trains[t];
            var starts = new List<GRBVar>();
            for (int u = 0; u < train.Count; u++) {
                int lb = distances[t][u];
                int ub = train[u].StartUb < 0 ? upperBound : train[u].StartUb;
                starts.Add(model.AddVar(lb, ub, 0, 'C', $"s_{t}_{u}"));
            }

            outerStarts.Add(starts);
            outerEnablers.Add(new Dictionary<(int, int), GRBVar>());

            var needsEnablers = -1;
            for (int u = 0; u < train.Count; u++) {
                if (needsEnablers < 0 && train[u].Successors.Count > 1) {
                    needsEnablers = u;
                }

                foreach (var v in train[u].Successors) {
                    int md = train[u].MinDuration;

                    if (needsEnablers >= 0) {
                        var enabler = model.AddVar(0, 1, 0, 'B', $"b_{u}_{v}");
                        // enabler.BranchPriority = 100;
                        outerEnablers[t][(u, v)] = enabler;
                        model.AddConstr(starts[v] >= starts[u] + md - (1 - enabler) * upperBound, $"aft_{u}_{v}");
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

        tq1.Finish();

        var tToChains = problem.FindResourceChains();
        var disjunctions =
            new Dictionary<(int, int, int, int, int, int), (int, GRBTempConstr, GRBTempConstr, string)>();
        var consToAdd = new List<(int, GRBTempConstr, GRBTempConstr, string)>();
        var tq2 = new Tqdm.ProgressBar(total: tToChains.Count, printsPerSecond: 4);
        tq2.SetLabel("Build disjunctives");

        foreach (var chains in tToChains.Values) {
            tq2.Step();
            for (int idx = 0; idx < chains.Count; idx++) {
                var (t1, u1, v1t, rt1) = chains[idx];
                // common for t1 == v1t but not always
                var v1succs = new List<int> { -1 };
                if (problem.Trains[t1][v1t].Successors.Count > 0)
                    v1succs = problem.Trains[t1][v1t].Successors;
                var u1s = outerStarts[t1][u1];
                var rt1a = Math.Max(0.1, rt1);
                foreach (var (t2, u2, v2t, rt2) in chains.Skip(idx + 1)) {
                    if (t2 == t1)
                        continue;
                    var rt2a = Math.Max(0.1, rt2);
                    GRBVar ch = null;
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

                            ch ??= model.AddVar(0, 1, 0, 'B', $"c_{t1}_{u1}_{t2}_{u2}");
                            oei1 -= upperBound * (1 - ch);
                            oei2 -= upperBound * ch;

                            var c1 = u2s >= v1s + rt1a + oei1;
                            var c2 = u1s >= v2s + rt2a + oei2;
                            var cname = $"dis_{t1}_{u1}_{t2}_{u2}_{v1}_{v2}";
                            var dis1 = distances[t1][u1];
                            var dis2 = distances[t2][u2];
                            consToAdd.Add((Math.Abs(dis1 - dis2), c1, c2, cname));
                            disjunctions[(t1, u1, v1, t2, u2, v2)] = consToAdd[^1];
                        }
                    }
                }
            }
        }

        tq2.Finish();

        consToAdd.Sort((a, b) => a.Item1.CompareTo(b.Item1));
        for (int t = 0; t < Math.Min(50000, consToAdd.Count); t++) {
            var (_, c1, c2, cname) = consToAdd[t];
            model.AddConstr(c1, cname + "_a");
            model.AddConstr(c2, cname + "_b");
        }

        Console.WriteLine("Added up to 50k of disjunctions: " + consToAdd.Count);

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
        return (model, outerStarts, outerEnablers, disjunctions);
    }

    class VerifyNoOverlapCallback : GRBCallback {
        private readonly List<GRBVar[]> _outerStarts;
        private readonly List<Dictionary<(int, int), GRBVar>> _outerEnablers;

        private readonly Dictionary<(int, int, int, int, int, int), (int, GRBTempConstr, GRBTempConstr, string)>
            _disjunctions;

        private readonly Problem _problem;

        private bool _wantsExit;

        public VerifyNoOverlapCallback(Problem problem, List<List<GRBVar>> outerStarts,
            List<Dictionary<(int, int), GRBVar>> enablers,
            Dictionary<(int, int, int, int, int, int), (int, GRBTempConstr, GRBTempConstr, string)> disjunctions) {
            _problem = problem;
            _outerStarts = outerStarts.Select(os => os.ToArray()).ToList();
            _outerEnablers = enablers;
            _disjunctions = disjunctions;

            Console.CancelKeyPress += (sender, e) => {
                Console.WriteLine("Ctrl+C detected, stopping optimization...");
                _wantsExit = true;
                e.Cancel = true; // Prevent immediate process termination
            };
        }

        [MethodImpl(MethodImplOptions.AggressiveOptimization)]
        protected override void Callback() {
            if (_wantsExit) {
                Abort();
                return;
            }

            if (where == GRB.Callback.MIPSOL) {
                try {
                    // key is res_name, value is start_time, stop_time, train, start_operation, end_operation
                    var resourceIntervals = new Dictionary<string, List<(double, double, int, int, int)>>();
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
                                            resourceIntervals[r.Name] = new List<(double, double, int, int, int)>();
                                        resourceIntervals[r.Name].Add((starts[u], starts[v], t, u, v));
                                    }

                                    u = v;
                                    break;
                                }
                            }
                        }
                    }

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
                            if (y1 < x2 || y2 < x1)
                                continue; // no overlap
                            Console.WriteLine(
                                $"Needed disjunction for {pair.Key} between {t1}, {u1}, {v1} and {t2}, {u2}, {v2}");
                            var key = (t1, u1, v1, t2, u2, v2);
                            if (!_disjunctions.ContainsKey(key))
                                key = (t2, u2, v2, t1, u1, v1);
                            var (_, c1, c2, cname) = _disjunctions[key];
                            AddLazy(c1);
                            AddLazy(c2);
                        }
                    }
                }
                catch (Exception e) {
                    Console.WriteLine("Error in callback: " + e);
                }
            }
        }
    }

    static Solution BuildAndOptimize(Problem problem, int maxTime, bool verbose) {
        var (model, outerStarts, outerEnablers, disjunctions) = BuildCpModel(problem, -1);
        GC.Collect(); // need all the RAM we can get
        model.Parameters.Threads = 8;
        model.Parameters.MemLimit = 32;
        // model.Parameters.Cuts = 0;
        // model.Parameters.Method = 2;
        // model.Parameters.Crossover = 1;
        // model.Parameters.Method = 1;
        // model.Parameters.Crossover = 0;
        model.Parameters.TimeLimit = maxTime;
        model.Parameters.LogToConsole = verbose ? 1 : 0;

        if (disjunctions.Count > 50000) {
            model.Parameters.LazyConstraints = 1;
            var cb = new VerifyNoOverlapCallback(problem, outerStarts, outerEnablers, disjunctions);
            model.SetCallback(cb);
        }

        model.Optimize();

        if (model.SolCount > 0) {
            return ExtractSolution(((GRBLinExpr)model.GetObjective()).Value, problem, outerStarts, outerEnablers);
        }

        var env = model.GetEnv();
        model.Dispose();
        env.Dispose();
        return null;
    }

    private static Solution ExtractSolution(double objectiveValue, Problem problem, List<List<GRBVar>> outerStarts,
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

                var value = (int)(outerStarts[t][u].X * 1000);
                solution.Events.Add(new Event { Operation = u, Time = value, Train = t });
            }
        }

        solution.Events.Sort((a, b) => {
            var ret = a.Time.CompareTo(b.Time);
            if (ret == 0)
                ret = a.Train.CompareTo(b.Train);
            if (ret == 0)
                ret = a.Operation.CompareTo(b.Operation);
            return ret;
        });
        foreach (var ev in solution.Events)
            ev.Time /= 1000;
        return solution;
    }

    static void Main() {
        // this approach fails because of a faulty assumption:
        // you can repair a failed solution by changing start times.
        // cutting the disjunctions instead makes unnecessary changes.
        // var problemFile = "../../../../../displib_instances_testing/displib_instances_testing/displib_testinstances_headway1.json";
        // var problemFile = "../../../../../displib_instances_phase1/line1_full_7.json";
        // var problemFile = "../../../../../displib_instances_phase1/line1_critical_6.json";
        var problemFile = "../../../../../displib_instances_phase2/line8_small_2.json";
        var problem = Problem.LoadFromFile(problemFile);
        Console.WriteLine("Building model for " + problem.Name);
        var solution = BuildAndOptimize(problem, 1000, true);
        if (solution != null) {
            var resultFile = $"results/{problem.Name}_solution.json";
            solution.WriteToFile(resultFile);
            Console.WriteLine("Solution found with objective: " + solution.ObjectiveValue);
        }
    }
}