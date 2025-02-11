// See https://aka.ms/new-console-template for more information

namespace balas;

using Shared;
using Gurobi;
using System.Linq;
using System;

class Program
{
    static (GRBModel model, List<List<GRBVar>> outerStarts, List<Dictionary<(int, int), GRBVar>> outerEnablers, Dictionary<(int, int, int, int), GRBVar>) 
        BuildCpModel(Problem problem, int maxGap)
    {
        int upperBound = problem.FindUpperBound();
        var distances = problem.FindShortestPaths();

        var env = new GRBEnv();
        env.LogToConsole = 1;
        env.Start();
        
        var model = new GRBModel(env);
        model.ModelName = problem.Name;
        
        var outerEnablers = new List<Dictionary<(int, int), GRBVar>>();
        var outerStarts = new List<List<GRBVar>>();
        
        for (int t = 0; t < problem.Trains.Count; t++)
        {
            var train = problem.Trains[t];
            var starts = new List<GRBVar>();
            for (int u = 0; u < train.Count; u++)
            {
                int lb = distances[t][u];
                int ub = train[u].StartUb < 0 ? upperBound : train[u].StartUb;
                starts.Add(model.AddVar(lb, ub, 0, 'C', $"s_{t}_{u}"));
            }
            outerStarts.Add(starts);
            outerEnablers.Add(new Dictionary<(int, int), GRBVar>());

            var needsEnablers = -1;
            for (int u = 0; u < train.Count; u++)
            {
                if (needsEnablers < 0 && train[u].Successors.Count > 1)
                {
                    needsEnablers = u;
                }
                foreach (var v in train[u].Successors)
                {
                    int md = train[u].MinDuration;
                    
                    if (needsEnablers >= 0)
                    {
                        var enabler = model.AddVar(0, 1, 0, 'B', $"b_{u}_{v}");
                        enabler.BranchPriority = 100; 
                        outerEnablers[t][(u, v)] = enabler;
                        model.AddConstr(starts[v] >= starts[u] + md - (1-enabler)*upperBound , $"aft_{u}_{v}");
                    }
                    else
                    {
                        model.AddConstr(starts[v] >= starts[u] + md, $"aft_{t}_{u}_{v}");
                    }
                }
            }

            if (needsEnablers >= 0)
            {
                for (var u = needsEnablers; u < train.Count; u++)
                {
                    var predecessors = new GRBLinExpr(0);
                    if (u > 0)
                    {
                        foreach (var p in train[u].Predecessors)
                        {
                            if (outerEnablers[t].TryGetValue((p, u), out var en))
                                predecessors += en;
                            else
                                predecessors += 1;
                        }
                        if (train[u].Predecessors.Count > 1)
                        {
                            model.AddConstr(predecessors <= 1, $"p_{t}_{u}");
                        }
                    }
                    else
                    {
                        predecessors += 1;
                    }
                    var successors = new GRBLinExpr(0);
                    if (u + 1 < train.Count)
                    {
                        foreach (var s in train[u].Successors)
                        {
                            if (outerEnablers[t].TryGetValue((u, s), out var en))
                                successors += en;
                            else
                                successors += 1;
                        }
                        if (train[u].Successors.Count > 1)
                        {
                            model.AddConstr(successors <= 1, $"s_{t}_{u}");
                        }
                    }
                    else
                    {
                        successors += 1;
                    }
                    model.AddConstr(predecessors == successors, $"ps_{t}_{u}");
                }
            }
        }

        var tToChains = problem.FindResourceChains();
        var disjunctions = new Dictionary<(int, int, int, int), GRBVar>();
        foreach (var chains in tToChains.Values)
        {
            for (int idx = 0; idx < chains.Count; idx++)
            {
                var (t1, u1, v1t, rt1) = chains[idx];
                var v1succs = new List<int>{-1};
                if (problem.Trains[t1][v1t].Successors.Count > 0)
                    v1succs = problem.Trains[t1][v1t].Successors;
                var u1s = outerStarts[t1][u1];
                foreach (var (t2, u2, v2t, rt2) in chains.Skip(idx + 1))
                {
                    if (t2 == t1)
                        continue;
                    GRBVar ch = null;
                    var v2succs = new List<int>{-1};
                    if (problem.Trains[t2][v2t].Successors.Count > 0)
                        v2succs = problem.Trains[t2][v2t].Successors;
                    var u2s = outerStarts[t2][u2];
                    
                    foreach (var v1 in v1succs)
                    {
                        foreach (var v2 in v2succs)
                        {
                            var v1s = v1 < 0 ? u1s + problem.Trains[t1][v1t].MinDuration : outerStarts[t1][v1];
                            var en1 = outerEnablers[t1].GetValueOrDefault((v1t, v1), null);
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
                            
                            model.AddConstr(u2s >= v1s + rt1 + oei1, $"dis1_{t1}_{u1}_{t2}_{u2}_{v1}_{v2}");
                            model.AddConstr(u1s >= v2s + rt2 + oei2, $"dis2_{t1}_{u1}_{t2}_{u2}_{v1}_{v2}");
                            disjunctions[((t1 << 16) | u1, (t1 << 16) | v1, (t2 << 16) | u2, (t2 << 16) | v2)] = ch;
                        }
                    }
                }
            }
        }

        Console.WriteLine("Added disjunctions: " + disjunctions.Count);

        var objectives = new GRBLinExpr(0);
        foreach (var objective in problem.Objectives)
        {
            var t = objective.Train;
            var u = objective.Operation;
            var ocv = model.AddVar(0, upperBound, 0, 'C', $"ocv_{t}_{u}");
            var ocb = model.AddVar(0, 1, 0, 'B', $"ocb_{t}_{u}");
            model.AddConstr(ocv >= outerStarts[t][u] - objective.Threshold - upperBound * (1 - ocb), $"obj_{t}_{u}");
            var enables = new GRBLinExpr(0);
            var found = 0;
            foreach (var p in problem.Trains[t][u].Predecessors)
                if (outerEnablers[t].TryGetValue((p, u), out var en))
                {
                    enables += en;
                    found++;
                }
            model.AddConstr(ocb >= enables + problem.Trains[t][u].Predecessors.Count - found, $"ob2_{t}_{u}");
            objectives += objective.Coeff * ocv + objective.Increment * ocb;
        }
        model.SetObjective(objectives, GRB.MINIMIZE);
        return (model, outerStarts, outerEnablers, disjunctions);
    }

    class EnCB : GRBCallback
    {
        public readonly GRBVar[] AllVariables;

        private readonly Graph baseGraph = new();
        private bool wantsExit;
        private int calls;
        private List<Dictionary<(int, int), GRBVar>> outerEnablers;
        private readonly Dictionary<(int, int), (int, bool)> choices = new();
        
        public EnCB(Problem problem, List<Dictionary<(int, int), GRBVar>> enablers, Dictionary<(int, int, int, int), GRBVar> disjunctions)
        {
            outerEnablers = enablers;

            var variables = new List<GRBVar>();
            for (int t = 0; t < problem.Trains.Count; t++) {
                baseGraph.AddEdge(-1, t << 16);
                for (int u = 1; u < problem.Trains[t].Count; u++) {
                    foreach (var p in problem.Trains[t][u].Predecessors) {
                        if (!enablers[t].ContainsKey((p, u)))
                            baseGraph.AddEdge((t << 16) | p, (t << 16) | u);
                        else {
                            choices[((t << 16) | p, (t << 16) | u)] = (variables.Count, false);
                            variables.Add(enablers[t][(p, u)]);
                        }
                    }
                }
            }

            foreach (var ((u1, v1, u2, v2), variable) in disjunctions) {
                choices[(u1, v1)] = (variables.Count, false);
                variables.Add(variable);
                choices[(u2, v2)] = (variables.Count, true);  // TODO: validate with choice
                variables.Add(variable);
            }
            
            AllVariables = variables.ToArray();
            
            Console.CancelKeyPress += (sender, e) =>
            {
                Console.WriteLine("Ctrl+C detected, stopping optimization...");
                wantsExit = true;
                e.Cancel = true; // Prevent immediate process termination
            };

        }
        protected override void Callback()
        {
            if (wantsExit) {
                Abort();
                return;
            }

            if (where == GRB.Callback.MIPSOL) {
                // verify no cycles:
                // build a graph using the enables.
                // then add the disjunctions using the choice vars.
                // then check for cycles.
                // if we have a cycle, add a cut that disallows the segments in the cycle that are enables or disjuncts.
                try {
                    var values = GetSolution(AllVariables);
                    var g = baseGraph.Clone();
                    foreach (var ((u, v), (index, invert)) in choices) {
                        if (!invert && values[index] > 0.5)
                            g.AddEdge(u, v);
                        else if (invert && values[index] < 0.5)
                            g.AddEdge(u, v);
                    }

                    var acyc = g.IsAcyclic(out var cycle);
                    if (!acyc) {
                        var lazyConstraint = new GRBLinExpr(0);
                        var found = 0;
                        for (int i = 1; i < cycle.Count; i++) {
                            if (choices.TryGetValue((cycle[i - 1], cycle[i]), out var pair)) {
                                var (idx, inv) = pair;
                                if (inv)
                                    lazyConstraint += 1 - AllVariables[idx];
                                else
                                    lazyConstraint += AllVariables[idx];
                                found++;
                            }
                            else if (choices.TryGetValue((cycle[i], cycle[i - 1]), out pair)) {
                                var (idx, inv) = pair;
                                if (!inv)
                                    lazyConstraint += 1 - AllVariables[idx];
                                else
                                    lazyConstraint += AllVariables[idx];
                                found++;
                            }
                        }

                        AddLazy(lazyConstraint <= found - 1);
                        Console.WriteLine("Cycled!");
                        return;
                    }

                    Console.WriteLine("Golden!");
                    return;
                }
                catch (Exception ex) {
                    Console.WriteLine("Exception! " + ex);
                }
            }
            
            if (where != GRB.Callback.MIPNODE || GetIntInfo(GRB.Callback.MIPNODE_STATUS) != GRB.Status.OPTIMAL) 
                return;
            
            // 20% chance to try to find a greedy solution:
            if (Random.Shared.NextSingle() < 0.8) {
                return;
            }

            return; // tmp

            // var vars = GetNodeRel(all_vars);
            // foreach (var key in enablerKeys) {
            //     if (vars[key] is > .25 and < 0.75) {
            //         return;
            //     }
            // }
            calls++;
            if (calls % 1000 == 0)
            {
                int good = 0;
                var values = outerEnablers.SelectMany(oe => oe.Values).ToArray();
                var rel = GetNodeRel(values);
                foreach (var en in rel)
                {
                    if (en is > .75 or < 0.25)
                    {
                        good++;
                    }
                }

                Console.WriteLine($"At {calls}: {good} / {values.Length}");
            }

        }

        public Graph GetFinalGraph() {
            var g = baseGraph.Clone();
            foreach (var ((u, v), (index, invert)) in choices) {
                if (!invert && AllVariables[index].X > 0.5)
                    g.AddEdge(u, v);
                else if (invert && AllVariables[index].X < 0.5)
                    g.AddEdge(u, v);
            }

            return g;
        }
    }

    static Solution BuildAndOptimize(Problem problem, int maxTime, bool verbose)
    {
        var (model, outerStarts, outerEnablers, disjunctions) = BuildCpModel(problem, -1);
        GC.Collect();  // need all the RAM we can get
        model.Parameters.Threads = 8;
        model.Parameters.MemLimit = 32;
        // model.Parameters.Cuts = 0;
        // model.Parameters.Method = 2;
        // model.Parameters.Crossover = 1;
        model.Parameters.Method = 1;
        model.Parameters.Crossover = 0;
        model.Parameters.TimeLimit = maxTime;
        model.Parameters.LazyConstraints = 1;

        var cb = new EnCB(problem, outerEnablers, disjunctions);
        model.SetCallback(cb);
        model.Optimize();
        
        if (model.SolCount > 0) {
            var lastGraph = cb.GetFinalGraph();
            var topoSort = lastGraph.TopologicalSort(-1);
            return ExtractSolution(((GRBLinExpr)model.GetObjective()).Value, problem, outerStarts, outerEnablers, topoSort);
        }
        var env = model.GetEnv();
        model.Dispose();
        env.Dispose();
        return null;
    }

    private static Solution ExtractSolution(double objectiveValue, Problem problem, List<List<GRBVar>> outerStarts,
        List<Dictionary<(int, int), GRBVar>> outerEnablers, List<int> topoSort) {
        var lookup = new Dictionary<int, int>();
        for(var i = 0; i < topoSort.Count; i++) {
            lookup[topoSort[i]] = i;
        }
        var solution = new Solution
        {
            ObjectiveValue = (int)Math.Floor(objectiveValue + 1e-5)
        };
        
        for (var t = 0; t < problem.Trains.Count; t++)
        {
            for (var u = 0; u < problem.Trains[t].Count; u++)
            {
                if (u > 0)
                {
                    var enables = 0.0;
                    foreach (var p in problem.Trains[t][u].Predecessors)
                        if (outerEnablers[t].ContainsKey((p, u)))
                        {
                            enables += outerEnablers[t][(p, u)].X;
                        }
                        else
                        {
                            enables += 1;
                            break;
                        }
                    if (enables < 0.5)
                        continue;
                }
                var value = (int)Math.Floor(outerStarts[t][u].X + 1e-5);
                solution.Events.Add(new Event { Operation = u, Time = value, Train = t });
            }
        }
        solution.Events.Sort((a, b) => {
            var ret = a.Time.CompareTo(b.Time);
            if (ret != 0)
                return ret;
            if (a.Train == b.Train)
                return a.Operation.CompareTo(b.Operation);

            var ha = lookup.TryGetValue((a.Train << 16) | a.Operation, out var la);
            var hb = lookup.TryGetValue((b.Train << 16) | b.Operation, out var lb);
            if (ha && hb)
                return la.CompareTo(lb);
            
            Console.WriteLine($"Missing keys {a.Train}, {a.Operation} to {b.Train}, {b.Operation}");
            return 0;
        });
        return solution;
    }

    static void Main() {
        
        // var problemFile = "../../../../../displib_instances_testing/displib_instances_testing/displib_testinstances_swapping1.json";
        //var problemFile = "../../../../../displib_instances_phase1/line1_full_7.json";
        var problemFile = "../../../../../displib_instances_phase1/line1_critical_5.json";
        var problem = Problem.LoadFromFile(problemFile);
        Console.WriteLine("Building model for " + problem.Name);
        var solution = BuildAndOptimize(problem, 1000, true);
        if (solution != null)
        {
            var resultFile = $"results/{problem.Name}_solution.json";
            solution.WriteToFile(resultFile);
            Console.WriteLine("Solution found with objective: " + solution.ObjectiveValue);
        }
    }
}
