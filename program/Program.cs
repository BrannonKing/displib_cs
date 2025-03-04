namespace program;

using Shared;
using Google.OrTools.Sat;
using TqdmSharp;

class Program {
    static (CpModel model, List<List<IntVar>> outerStarts, List<Dictionary<(int, int), LinearExpr>> outerEnablers)
        BuildCpModel(Problem problem, int maxGap) {
        int upperBound = problem.FindUpperBound();
        var distances = problem.FindShortestPaths();

        var model = new CpModel();
        model.Model.Name = problem.Name;

        var outerEnablers = new List<Dictionary<(int, int), LinearExpr>>();
        var outerStarts = new List<List<IntVar>>();
        var durationSum = 0;
        var durationsAdded = 0;

        for (int t = 0; t < problem.Trains.Count; t++) {
            var train = problem.Trains[t];
            var starts = new List<IntVar>();
            for (int u = 0; u < train.Count; u++) {
                int lb = distances[t][u];
                int ub = train[u].StartUb < 0 ? upperBound : train[u].StartUb;
                starts.Add(model.NewIntVar(lb, ub, $"s_{t}_{u}"));
            }

            outerStarts.Add(starts);
            outerEnablers.Add(new Dictionary<(int, int), LinearExpr>());

            var needsEnablers = -1;
            for (int u = 0; u < train.Count; u++) {
                if (needsEnablers < 0 && train[u].Successors.Count > 1) {
                    needsEnablers = u;
                }

                foreach (var v in train[u].Successors) {
                    int md = train[u].MinDuration;
                    durationSum += md;
                    durationsAdded++;
                    var added = model.Add(starts[v] >= starts[u] + md);
                    if (needsEnablers >= 0) {
                        var enabler = model.NewBoolVar($"b_{u}_{v}");
                        outerEnablers[t][(u, v)] = enabler;
                        added.OnlyEnforceIf(enabler);
                    }
                }
            }

            if (needsEnablers >= 0) {
                for (var u = needsEnablers; u < train.Count; u++) {
                    LinearExpr predecessors = model.NewConstant(1);
                    if (u > 0) {
                        var preds = train[u].Predecessors.Select(p =>
                            outerEnablers[t].GetValueOrDefault((p, u), model.NewConstant(1))).ToList();
                        predecessors = LinearExpr.Sum(preds);
                        if (preds.Count > 1) {
                            model.Add(predecessors <= 1);
                        }
                    }

                    LinearExpr successors = model.NewConstant(1);
                    if (u + 1 < train.Count) {
                        var succs = train[u].Successors.Select(s =>
                            outerEnablers[t].GetValueOrDefault((u, s), model.NewConstant(1))).ToList();
                        successors = LinearExpr.Sum(succs);
                        if (succs.Count > 1) {
                            model.Add(successors <= 1);
                        }
                    }

                    model.Add(predecessors == successors);
                }
            }
        }
        var durationAverage = durationSum / durationsAdded;

        var tToChains = problem.FindResourceChains();
        var disjunctions = 0;
        var gapped = 0;
        foreach (var chains in Tqdm.Wrap(tToChains.Values)) {
            for (int idx = 0; idx < chains.Count; idx++) {
                var (t1, u1, v1t, rt1) = chains[idx];
                var v1succs = new List<int> { -1 };
                if (problem.Trains[t1][v1t].Successors.Count > 0)
                    v1succs = problem.Trains[t1][v1t].Successors;
                var u1s = outerStarts[t1][u1];
                rt1 = Math.Max(1, rt1);
                foreach (var (t2, u2, v2t, rt2) in chains.Skip(idx + 1)) {
                    if (t2 == t1)
                        continue;
                    
                    BoolVar ch = null;
                    var v2succs = new List<int> { -1 };
                    if (problem.Trains[t2][v2t].Successors.Count > 0)
                        v2succs = problem.Trains[t2][v2t].Successors;
                    var u2s = outerStarts[t2][u2];
                    var rt2a = Math.Max(1, rt2);

                    foreach (var v1 in v1succs) {
                        foreach (var v2 in v2succs) {
                            
                            LinearExpr v1s = v1 < 0 ? u1s + problem.Trains[t1][v1t].MinDuration : outerStarts[t1][v1];
                            var en1 = (ILiteral)outerEnablers[t1].GetValueOrDefault((v1t, v1), null);
                            var oei1 = new List<ILiteral>();
                            if (en1 != null)
                                oei1.Add(en1);

                            LinearExpr v2s = v2 < 0 ? u2s + problem.Trains[t2][v2t].MinDuration : outerStarts[t2][v2];
                            var en2 = (ILiteral)outerEnablers[t2].GetValueOrDefault((v2t, v2), null);
                            var oei2 = new List<ILiteral>();
                            if (en2 != null)
                                oei2.Add(en2);
                            
                            // we have to filter some of these out, and we have to be smart about it.
                            // if v1 is way before u2, and there is 20% the room necessary between them, let's just assume
                            // that the item will get done in that order.
                            var d1v1 = 0;
                            var d2u2 = 0;
                            if (v1 >= 0 && v2 >= 0) {
                                d1v1 = distances[t1][v1];
                                d2u2 = distances[t2][u2];
                                // if (d2u2 - d1v1 > 10 * durationAverage + rt1) {
                                //     var c1 = model.Add(u2s >= v1s + rt1);
                                //     if (oei1.Count > 0)
                                //         c1.OnlyEnforceIf(oei1.ToArray());
                                //     gapped++;
                                //     continue;
                                // }
                                //
                                // var d1u1 = distances[t1][u1];
                                // var d2v2 = distances[t2][v2];
                                // if (d1u1 - d2v2 > 10 * durationAverage + rt2a) {
                                //     var c1 = model.Add(u1s >= v2s + rt2a);
                                //     if (oei2.Count > 0)
                                //         c1.OnlyEnforceIf(oei2.ToArray());
                                //     gapped++;
                                //     continue;
                                // }
                            }

                            if (ch == null) {
                                ch = model.NewBoolVar($"c_{t1}_{u1}_{t2}_{u2}");
                                // ch == 1 implies u2 after v1
                                model.AddHint(ch, d1v1 < d2u2);
                            }

                            oei1.Add(ch);
                            oei2.Add(ch.Not());
                            model.Add(u2s >= v1s + rt1).OnlyEnforceIf(oei1.ToArray());
                            model.Add(u1s >= v2s + rt2a).OnlyEnforceIf(oei2.ToArray());
                            disjunctions++;
                        }
                    }
                }
            }
        }

        Console.WriteLine("Added disjunctions: " + disjunctions + ", Gapped:" + gapped);

        var objectives = new List<LinearExpr>();
        foreach (var objective in problem.Objectives) {
            var t = objective.Train;
            var u = objective.Operation;
            var ocv = model.NewIntVar(0, upperBound, $"ocv_{t}_{u}");
            var ocb = model.NewBoolVar($"ocb_{t}_{u}");
            model.Add(ocv >= outerStarts[t][u] - objective.Threshold).OnlyEnforceIf(ocb);
            var enables = new List<LinearExpr>();
            foreach (var p in problem.Trains[t][u].Predecessors)
                if (outerEnablers[t].ContainsKey((p, u)))
                    enables.Add(outerEnablers[t][(p, u)]);

            model.Add(ocb >= LinearExpr.Sum(enables) + problem.Trains[t][u].Predecessors.Count - enables.Count);
            objectives.Add(objective.Coeff * ocv + objective.Increment * ocb);
        }

        model.Minimize(LinearExpr.Sum(objectives));
        return (model, outerStarts, outerEnablers);
    }

    static Solution BuildAndOptimize(Problem problem, int maxTime, bool verbose) {
        var solver = new CpSolver();
        var (model, outerStarts, outerEnablers) = BuildCpModel(problem, -1);
        solver.StringParameters =
            $"num_workers:8,linearization_level:0,optimize_with_core:false,symmetry_level:2,max_time_in_seconds:{maxTime},log_search_progress:{verbose}";
        var status = solver.Solve(model);

        if (status is CpSolverStatus.Feasible or CpSolverStatus.Optimal) {
            return ExtractSolution(solver, problem, outerStarts, outerEnablers);
        }

        return null;
    }

    private static Solution ExtractSolution(CpSolver solver, Problem problem, List<List<IntVar>> outerStarts,
        List<Dictionary<(int, int), LinearExpr>> outerEnablers) {
        var solution = new Solution { };
        solution.ObjectiveValue = (int)Math.Round(solver.ObjectiveValue);

        for (int t = 0; t < problem.Trains.Count; t++) {
            for (int u = 0; u < problem.Trains[t].Count; u++) {
                if (u > 0) {
                    int enables = 0;
                    foreach (var p in problem.Trains[t][u].Predecessors) {
                        if (outerEnablers[t].ContainsKey((p, u))) {
                            enables += (int)solver.Value(outerEnablers[t][(p, u)]);
                        }
                        else {
                            enables += 1;
                            break;
                        }
                    }

                    if (enables < 1)
                        continue;
                }

                int value = (int)solver.Value(outerStarts[t][u]);
                solution.Events.Add(new Event { Operation = u, Time = value, Train = t });
            }
        }

        solution.Events.Sort((a, b) => {
            var ret = solver.Value(outerStarts[a.Train][a.Operation]).CompareTo(solver.Value(outerStarts[b.Train][b.Operation]));
            return ret == 0 ? a.Operation.CompareTo(b.Operation) : ret;
        });
        return solution;
    }

    static void Main() {
        // var problemFile = "../../../../../displib_instances_testing/displib_instances_testing/displib_testinstances_swapping2.json";
        // var problemFile = "../../../../../displib_instances_phase1/line1_critical_6.json";
        // var problemFile = "../../../../../displib_instances_phase1/line1_full_7.json";
        var problemFile = "../../../../../displib_instances_phase1/line3_5.json";
        // var problemFile = "../../../../../displib_instances_phase2/line8_large_4.json";
        // var problemFile = "../../../../../displib_instances_phase2/line3_7.json";
        var problem = Problem.LoadFromFile(problemFile);
        Console.WriteLine("Building model for " + problem.Name);
        Solution solution = BuildAndOptimize(problem, 600, true);
        if (solution != null) {
            var resultFile = $"results/{problem.Name}_solution_ort.json";
            solution.WriteToFile(resultFile);
            Console.WriteLine("Solution found with objective: " + solution.ObjectiveValue);
        }
    }
}