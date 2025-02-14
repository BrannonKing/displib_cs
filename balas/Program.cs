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
                        var v1s = v1 < 0 ? u1s + problem.Trains[t1][v1t].MinDuration : outerStarts[t1][v1];
                        var en1 = outerEnablers[t1].GetValueOrDefault((v1t, v1), null);
                        foreach (var v2 in v2succs)
                        {
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

    class BalasCallback : GRBCallback
    {
        private readonly GRBVar[] _allVariables;
        private readonly Graph _baseGraph = new();
        private readonly List<Dictionary<(int, int), GRBVar>> _outerEnablers;
        private readonly Dictionary<(int, int), (int, bool)> _choices = new();
        private readonly int _enablerChoices;
        private readonly Problem _problem;
        private readonly Dictionary<(int, int), (int, int)> _disjunctPairs = new();

        private bool _wantsExit;
        private int _calls;

        public BalasCallback(Problem problem, List<Dictionary<(int, int), GRBVar>> enablers, Dictionary<(int, int, int, int), GRBVar> disjunctions)
        {
            _outerEnablers = enablers;
            _problem = problem;

            var variables = new List<GRBVar>();
            for (int t = 0; t < problem.Trains.Count; t++) {
                _baseGraph.AddEdge(-1, t << 16);
                for (int u = 1; u < problem.Trains[t].Count; u++) {
                    foreach (var p in problem.Trains[t][u].Predecessors) {
                        if (!enablers[t].ContainsKey((p, u)))
                            _baseGraph.AddEdge((t << 16) | p, (t << 16) | u);
                        else {
                            _choices[((t << 16) | p, (t << 16) | u)] = (variables.Count, false);
                            variables.Add(enablers[t][(p, u)]);
                        }
                    }
                }
            }

            _enablerChoices = variables.Count;
            
            foreach (var ((u1, v1, u2, v2), variable) in disjunctions) {
                _disjunctPairs[(v1, u2)] = (v2, u1);
                _disjunctPairs[(v2, u1)] = (v1, u2);
                
                _choices[(v1, u2)] = (variables.Count, false);
                variables.Add(variable);
                _choices[(v2, u1)] = (variables.Count, true);  // TODO: validate with choice
                variables.Add(variable);
            }
            
            _allVariables = variables.ToArray();
            
            Console.CancelKeyPress += (sender, e) =>
            {
                Console.WriteLine("Ctrl+C detected, stopping optimization...");
                _wantsExit = true;
                e.Cancel = true; // Prevent immediate process termination
            };

        }
        protected override void Callback()
        {
            if (_wantsExit) {
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
                    var values = GetSolution(_allVariables);
                    var g = _baseGraph.Clone();
                    foreach (var ((u, v), (index, invert)) in _choices) {
                        if (!invert && values[index] >= 0.5)
                            g.AddEdge(u, v);
                        else if (invert && values[index] < 0.5)
                            g.AddEdge(u, v);
                    }

                    var acyclic = g.IsAcyclic(-1, out var cycle);
                    if (!acyclic) {
                        var lazyConstraint = new GRBLinExpr(0);
                        var found = 0;
                        for (int i = 1; i < cycle.Count; i++) {
                            if (_choices.TryGetValue((cycle[i - 1], cycle[i]), out var pair)) {
                                var (idx, inv) = pair;
                                if (inv)
                                    lazyConstraint += (1 - _allVariables[idx]);
                                else
                                    lazyConstraint += _allVariables[idx];
                                found++;
                            }
                        }

                        AddLazy(lazyConstraint <= found - 1);
                        // Console.WriteLine("Cycled!");
                        return;
                    }

                    // Console.WriteLine("Golden! Burn it down!");
                    // // var score = (int)Math.Round(GetDoubleInfo(GRB.Callback.MIPSOL_OBJBST));
                    // var score = 1000000000; 
                    // var success = BurnDown(g, score, values);
                    // if (success) {
                    //     SetSolution(_allVariables, values);
                    //     var objective = UseSolution();
                    //     if (objective < GRB.INFINITY) {
                    //         Console.WriteLine("We found one! Objective: " + objective);
                    //     }
                    // }
                    return;
                }
                catch (Exception ex) {
                    Console.WriteLine("Exception! " + ex);
                }
            }
            
            if (where != GRB.Callback.MIPNODE || GetIntInfo(GRB.Callback.MIPNODE_STATUS) != GRB.Status.OPTIMAL) 
                return;
            
            // chance to try to find a greedy solution:
            if (Random.Shared.NextSingle() < 0.95) {
                return;
            }

            var nodeValues = GetNodeRel(_allVariables);
            for (var i = 0; i < _enablerChoices; i++) {
                if (nodeValues[i] is > .25 and < 0.75) {
                    return;
                }
            }
            
            // build a graph with the chosen paths. Then complete the disjunctions for it.
            var nodeG = _baseGraph.Clone();
            var disjuncts = new List<(Edge, Edge)>();
            foreach (var ((u, v), (index, invert)) in _choices) {
                if (nodeValues[index] is <= .25 or >= 0.75) {
                    if (!invert && nodeValues[index] >= 0.75)
                        nodeG.AddEdge(u, v);
                    else if (invert && nodeValues[index] <= 0.25)
                        nodeG.AddEdge(u, v);
                }
                else {
                    var far = _disjunctPairs[(u, v)];
                    var farEdge = new Edge(far.Item1, far.Item2);
                    // we'll hit a choice for the far edge later, and we want to skip that one.
                    if (nodeG.HasEdge(far.Item1, far.Item2))
                        continue;
                    disjuncts.Add((new Edge(u, v), farEdge));
                }
            }

            var noCycles = nodeG.AddReversibleEdgesWithBacktracking(disjuncts);
            if (noCycles) {
                for (int i = 0; i < nodeValues.Length; i++) {
                    nodeValues[i] = Math.Round(nodeValues[i]);
                }

                foreach (var (edge1, edge2) in disjuncts) {
                    double one = 1.0, zero = 0.0;
                    if (nodeG.HasEdge(edge2.U, edge2.V)) {
                        one = 0.0;
                        zero = 1.0;
                    }
                    var (index, invert) = _choices[(edge1.U, edge1.V)];
                    nodeValues[index] = invert ? zero : one;
                    (index, invert) = _choices[(edge2.U, edge2.V)];
                    nodeValues[index] = invert ? one : zero;
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

        private (List<int>, int) GetLongestPath(Graph graph) {
            var topoSort = graph.TopologicalSort(-1);
            if (topoSort == null) {
                return (null, 1000000000);
            }
            var distances = new Dictionary<int, int>();
            var prevs = new Dictionary<int, int>();
            distances[-1] = 0;
            foreach (var u in topoSort) {
                var tu = u >> 16;
                foreach (var v in graph.Successors(u)) {
                    var tv = v >> 16;
                    var cost = 0;
                    var lb = 0;
                    if (tu == tv) {
                        cost = _problem.Trains[tu][u & 0xffff].MinDuration;
                        lb = _problem.Trains[tu][u & 0xffff].StartLb;
                    }
                    var cumulative = Math.Max(distances[u] + cost, lb);
                    if (!distances.TryGetValue(v, out var value) || value < cumulative) {
                        distances[v] = cumulative;
                        prevs[v] = u;
                    }
                }
            }
            
            // find the key in distances having the largest value:
            var max = distances.Aggregate((l, r) => l.Value > r.Value ? l : r).Key;
            var maxDistance = distances[max];
            var path = new List<int>();
            while (max != -1) {
                path.Add(max);
                max = prevs[max];
            }

            path.Reverse();
            return (path, maxDistance);
        }

        private (int, IEnumerable<(int, int)>) RecursiveBurnDown(Graph graph, Dictionary<(int, int), int> keepers, int bestScore) {
            // for each pair in the longest path
            // if it is swappable (a disjunction) and not swapped yet
            // remove that edge and add the reverse
            // score = recurse
            // if score is better store the swap
            // restore the original edge and remove its reverse
            var (path, cost) = GetLongestPath(graph);
            if (cost >= bestScore) {
                return (cost, null);
            }

            bestScore = cost;
            IEnumerable<(int, int)> bestSwaps = null;
            for (var i = 1; i < path.Count; ++i) {
                var (u, v) = (path[i - 1], path[i]);
                if (_disjunctPairs.ContainsKey((u, v))) {
                    if (keepers.ContainsKey((u, v)))
                        continue;
                    graph.RemoveEdge(u, v);
                    var opposite = _disjunctPairs[(u, v)];
                    graph.AddEdge(opposite.Item1, opposite.Item2);
                    keepers[opposite] = 1;
                    var (score, swaps) = RecursiveBurnDown(graph, keepers, bestScore);
                    if (score < bestScore) {
                        bestScore = score;
                        bestSwaps = new List<(int, int)> { (u, v) };
                        if (swaps != null)
                            bestSwaps = bestSwaps.Concat(swaps);
                    }
                    graph.RemoveEdge(opposite.Item1, opposite.Item2);
                    graph.AddEdge(u, v);
                    // we can run with and without this next line.
                    // without it, we search a smaller space, and that would be good if we knew
                    // that it was rare for this to enable a better solution. 
                    keepers.Remove(opposite);
                }
            }
            return (bestScore, bestSwaps);
        }

        private bool BurnDown(Graph graph, int score, double[] values) {
            var keepers = new Dictionary<(int, int), int>();
            var (reducedScore, swaps) = RecursiveBurnDown(graph, keepers, score);
            if (swaps != null && reducedScore > 0 && reducedScore < score) {
                Console.WriteLine($"Found better solution of {reducedScore} < {score}.");
                foreach (var swap in swaps) {
                    var (index, inv) = _choices[swap];
                    values[index] = inv ? 1.0 : 0.0;
                    (index, inv) = _choices[_disjunctPairs[swap]];
                    values[index] = inv ? 0.0 : 1.0;
                }
                return true;
            }
            return false;
        }

        public Graph GetFinalGraph() {
            var g = _baseGraph.Clone();
            foreach (var ((u, v), (index, invert)) in _choices) {
                if (!invert && _allVariables[index].X > 0.5)
                    g.AddEdge(u, v);
                else if (invert && _allVariables[index].X < 0.5)
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
        // model.Parameters.Method = 1;
        // model.Parameters.Crossover = 0;
        model.Parameters.TimeLimit = maxTime;
        model.Parameters.LazyConstraints = 1;

        var cb = new BalasCallback(problem, outerEnablers, disjunctions);
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
        
        //var problemFile = "../../../../../displib_instances_testing/displib_instances_testing/displib_testinstances_headway1.json";
        //var problemFile = "../../../../../displib_instances_phase1/line1_full_7.json";
        var problemFile = "../../../../../displib_instances_phase1/line1_critical_6.json";
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
