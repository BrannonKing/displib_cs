namespace balas;

using System;
using System.Collections.Generic;

// necessary functions:
// 1. add edge from 4 int16
// 2. add edge from 2 int
// 3. topologocial sort
// 4. deduplicate edge list, keeping the largest weight
// 5. greedily resolve any disjunctives
// 6. greedily resolve any disjunctives with enablements as well

// Represents a directed edge from U to V.
public class Edge(int u, int v) {
    public int U { get; } = u;
    public int V { get; } = v;

    public override bool Equals(object obj) {
        if (obj is Edge other) {
            return this.U == other.U && this.V == other.V;
        }

        return false;
    }

    public override int GetHashCode() {
        return U.GetHashCode() * 307 + V.GetHashCode();
    }

    public override string ToString() {
        return $"({U}, {V})";
    }
}

// A simple directed graph using an adjacency list.
public class Graph {
    // Dictionary: node -> list of outgoing neighbors.
    private Dictionary<int, List<int>> _adj = new();

    public Graph Clone() {
        var clone = new Graph {
            _adj = _adj.ToDictionary(kvp => kvp.Key, kvp => new List<int>(kvp.Value))
        };
        return clone;
    }

    // Adds an edge from u to v.
    public void AddEdge(int u, int v) {
        if (!_adj.TryGetValue(u, out var value)) {
            value = new List<int>();
            _adj[u] = value;
        }

        if (!value.Contains(v))
            value.Add(v);

        // Ensure v appears in the dictionary (even if it has no outgoing edges). Why?
        if (!_adj.ContainsKey(v)) {
            _adj[v] = new List<int>();
        }
    }
    
    public bool HasEdge(int u, int v) {
        return _adj.TryGetValue(u, out var value) && value.Contains(v);
    }
    
    public IReadOnlyList<int> Successors(int u) {
        return _adj.TryGetValue(u, out var value) ? value : new List<int>();
    }

    // Removes the edge from u to v.
    public void RemoveEdge(int u, int v) {
        if (_adj.TryGetValue(u, out var value)) {
            value.Remove(v);
        }
    }

    // Returns all the edges in the graph.
    public IEnumerable<Edge> GetEdges() {
        foreach (var kvp in _adj) {
            var u = kvp.Key;
            foreach (var v in kvp.Value) {
                yield return new Edge(u, v);
            }
        }
    }

    /// <summary>
    /// Checks whether the graph is acyclic.
    /// If a cycle is found, it returns false and outputs one cycle (as a list of nodes, with the first and last node being the same).
    /// </summary>
    public bool IsAcyclic(int? start, out List<int> cycle) {
        cycle = null;
        // 0 = unvisited, 1 = visiting, 2 = visited.
        var state = new Dictionary<int, int>();
        foreach (var node in _adj.Keys) {
            state[node] = 0;
        }
        
        var path = new List<int>();
        if (start.HasValue) {
            if (!DfsVisit(start.Value, state, path, out cycle))
                return false;
        }
        else {
            foreach (var node in _adj.Keys) {
                if (state[node] == 0) {
                    if (!DfsVisit(node, state, path, out cycle))
                        return false;
                }
            }
        }

        return true;
    }

    public void ValidateUnique() {
        foreach (var kvp in _adj) {
            var u = kvp.Key;
            var neighbors = kvp.Value;
            var unique = new HashSet<int>(neighbors);
            if (unique.Count != neighbors.Count) {
                throw new Exception($"Node {u} has duplicate neighbors.");
            }
        }
    }

    /// <summary>
    /// DFS helper method that tracks the recursion path.
    /// When a back edge is detected (neighbor in the current path), a cycle is reconstructed and returned.
    /// </summary>
    private bool DfsVisit(int node, Dictionary<int, int> state, List<int> path, out List<int> cycle) {
        state[node] = 1; // Mark as visiting.
        path.Add(node);

        if (_adj.TryGetValue(node, out var neighbors)) {
            foreach (var neighbor in neighbors) {
                if (state[neighbor] == 0) {
                    if (!DfsVisit(neighbor, state, path, out cycle))
                        return false;
                }
                else if (state[neighbor] == 1) {
                    // Found a back edge; extract the cycle from the current path.
                    var startIndex = path.IndexOf(neighbor);
                    cycle = new List<int>();
                    for (var i = startIndex; i < path.Count; i++) {
                        cycle.Add(path[i]);
                    }

                    // Add the neighbor at the end to show the complete cycle.
                    cycle.Add(neighbor);
                    return false;
                }
            }
        }

        state[node] = 2; // Mark as visited.
        path.RemoveAt(path.Count - 1);
        cycle = null;
        return true;
    }
    
    // Prints all the edges.
    public void PrintEdges() {
        Console.WriteLine("Graph edges:");
        foreach (var e in GetEdges()) {
            Console.WriteLine(e);
        }
    }
    
    /// <summary>
    /// Computes the topological sort of the graph.
    /// Assumes the graph is acyclic; otherwise, the result is undefined.
    /// </summary>
    public List<int> TopologicalSort(int? start = null)
    {
        // Use DFS-based postorder traversal.
        var visited = new Dictionary<int, int>();
        foreach (var node in _adj.Keys)
            visited[node] = 0;
        var sorted = new List<int>();

        if (start.HasValue) {
            if (!TopologicalSortDfs(start.Value, visited, sorted))
                return null;
        }
        else {
            foreach (var node in _adj.Keys) {
                if (visited[node] == 0) {
                    if (!TopologicalSortDfs(node, visited, sorted))
                        return null;
                }
            }
        }

        // Reverse the postorder to get the topological order.
        sorted.Reverse();
        return sorted;
    }

    /// <summary>
    /// Helper DFS method for topological sorting.
    /// </summary>
    private bool TopologicalSortDfs(int node, Dictionary<int, int> visited, List<int> sorted)
    {
        visited[node] = 1;
        if (_adj.TryGetValue(node, out var neighbors))
        {
            foreach (var neighbor in neighbors)
            {
                if (visited[neighbor] == 0) {
                    if (!TopologicalSortDfs(neighbor, visited, sorted))
                        return false;
                }
                else if (visited[neighbor] == 1) {
                    return false;
                }
            }
        }
        visited[node] = 2;
        sorted.Add(node);
        return true;
    }


    /// <summary>
    /// Adds one edge from each disjunctive pair to the DAG, using backtracking when necessary.
    /// Each disjunctive pair is represented as a Tuple of two possible Edge objects.
    /// The algorithm tries first the edge with the smallest absolute difference between u and v.
    /// </summary>
    /// <param name="disjunctiveEdges">A list of disjunctive edge pairs.</param>
    /// <returns>The modified graph with added edges.</returns>
    public bool AddReversibleEdgesWithBacktracking(List<(Edge, Edge)> disjunctiveEdges) {

        var precheck = IsAcyclic(-1, out _);
        if (!precheck) {
            throw new Exception("It had a cycle!");
        }

        
        var index = 0;
        // This list keeps track of the edges we have successfully added for each disjunctive pair.
        var selectedEdges = new List<Edge>();
        // Keep track of edges that have already been attempted and failed.
        var skippedEdges = new HashSet<Edge>();

        while (index < disjunctiveEdges.Count) {
            var pair = disjunctiveEdges[index];
            // Get the two possible edges.
            var edge1 = pair.Item1;
            var edge2 = pair.Item2;

            // Greedy heuristic: try the edge with the smaller absolute difference between endpoints first.
            if (Math.Abs((edge1.U & 0xffff) - (edge1.V & 0xffff)) > Math.Abs((edge2.U & 0xffff) - (edge2.V & 0xffff))) {
                // Swap to ensure edge1 has the smaller difference.
                (edge1, edge2) = (edge2, edge1);
            }

            var added = false;

            // Try the first option if not already skipped.
            if (!skippedEdges.Contains(edge1)) {
                AddEdge(edge1.U, edge1.V);
                if (IsAcyclic(edge1.V, out _)) {
                    selectedEdges.Add(edge1);
                    index++; // Move to the next disjunctive pair.
                    added = true;
                }
                else {
                    RemoveEdge(edge1.U, edge1.V);
                    skippedEdges.Add(edge1);
                }
            }

            // If the first option didn't work, try the second.
            if (!added && !skippedEdges.Contains(edge2)) {
                AddEdge(edge2.U, edge2.V);
                if (IsAcyclic(edge2.V, out _)) {
                    selectedEdges.Add(edge2);
                    index++; // Move to the next disjunctive pair.
                    added = true;
                }
                else {
                    RemoveEdge(edge2.U, edge2.V);
                    skippedEdges.Add(edge2);
                }
            }

            // If neither option worked, backtrack.
            if (!added) {
                if (selectedEdges.Count > 0) {
                    // Remove the last successfully added edge.
                    var lastAdded = selectedEdges[^1];
                    selectedEdges.RemoveAt(selectedEdges.Count - 1);
                    RemoveEdge(lastAdded.U, lastAdded.V);
                    skippedEdges.Add(lastAdded);
                    index--; // Backtrack to the previous disjunctive pair.
                }
                else {
                    // throw new Exception("Cannot add edges without creating a cycle.");
                    return false;
                }
            }
        }

        var test = IsAcyclic(-1, out _);
        if (!test) {
            throw new Exception("It had a cycle!");
        }
        return true;
    }

    // static void Main(string[] args)
    // {
    //     // Create a simple DAG.
    //     var G = new Graph();
    //     // Base DAG edges.
    //     G.AddEdge(1, 2);
    //     G.AddEdge(2, 3);
    //     G.AddEdge(3, 4);
    //
    //     // Define disjunctive edges.
    //     // Each Tuple contains two alternative edges.
    //     // For example, for the pair ((1,3), (3,1)), one of these will be added.
    //     var disjunctiveEdges = new List<Tuple<Edge, Edge>>
    //     {
    //         new Tuple<Edge, Edge>(new Edge(1, 3), new Edge(3, 1)),
    //         new Tuple<Edge, Edge>(new Edge(2, 4), new Edge(4, 2)),
    //         new Tuple<Edge, Edge>(new Edge(3, 5), new Edge(5, 3))
    //     };
    //
    //     try
    //     {
    //         Graph modifiedGraph = AddReversibleEdgesWithBacktracking(G, disjunctiveEdges);
    //         modifiedGraph.PrintEdges();
    //     }
    //     catch (Exception ex)
    //     {
    //         Console.WriteLine("Error: " + ex.Message);
    //     }
    //
    //     Console.WriteLine("Press any key to exit.");
    //     Console.ReadKey();
    // }
}