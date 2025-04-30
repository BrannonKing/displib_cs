namespace with_rt;

using System;
using System.Collections.Generic;
using System.Linq;

public class Digraph<T>
{
    // adjacency list, using hash‐sets so we can union in place without dupes
    private readonly Dictionary<T, HashSet<T>> _adj = new();

    /// <summary>
    /// Add a node (if not already present).
    /// </summary>
    public void AddNode(T u)
    {
        if (!_adj.ContainsKey(u))
            _adj[u] = new HashSet<T>();
    }

    /// <summary>
    /// Add a directed edge u → v. Automatically adds u and v as nodes if needed.
    /// </summary>
    public void AddEdge(T u, T v)
    {
        AddNode(u);
        AddNode(v);
        _adj[u].Add(v);
    }

    /// <summary>
    /// Computes the transitive closure by augmenting the existing adjacency sets.
    /// After calling this, _adj[u] contains all original successors of u _and_ all
    /// nodes reachable via any path from u.
    /// </summary>
    public void ComputeTransitiveClosureInPlace()
    {
        // 1. Topological sort (Kahn's algorithm)
        var indegree = _adj.Keys.ToDictionary(u => u, _ => 0);
        foreach (var u in _adj.Keys)
            foreach (var v in _adj[u])
                indegree[v] = indegree.GetValueOrDefault(v) + 1;

        var q = new Queue<T>(indegree.Where(kv => kv.Value == 0).Select(kv => kv.Key));
        var topo = new List<T>();
        while (q.Count > 0)
        {
            var u = q.Dequeue();
            topo.Add(u);
            foreach (var v in _adj[u])
            {
                indegree[v]--;
                if (indegree[v] == 0)
                    q.Enqueue(v);
            }
        }

        // 2. Compute closures locally
        var closure = new Dictionary<T, HashSet<T>>();
        foreach (var u in topo.AsEnumerable().Reverse())
        {
            var reach = new HashSet<T>();
            foreach (var v in _adj[u])
            {
                reach.Add(v);                             // direct edge
                if (closure.TryGetValue(v, out var vr))   // plus everything v can reach
                    reach.UnionWith(vr);
            }
            closure[u] = reach;
        }

        // 3. Augment the original adjacency sets in place
        foreach (var u in closure.Keys.ToList())
        {
            _adj[u].UnionWith(closure[u]);
        }
    }

    /// <summary>
    /// Returns true iff there is a path u →* v in the graph.
    /// ComputeTransitiveClosureInPlace() must have been called first.
    /// </summary>
    public bool IsReachable(T u, T v)
    {
        if (!_adj.TryGetValue(u, out var value))
            throw new InvalidOperationException("Unknown node: " + u);
        return value.Contains(v);
    }
}