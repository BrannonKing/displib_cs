namespace with_rt;

using System;
using System.Collections.Generic;
using System.Linq;

public class Digraph<T>
{
    private readonly Dictionary<T, HashSet<T>> _adj = new();
    private int _time = 0;
    private Dictionary<T, int> _disc; // Discovery times
    private Dictionary<T, int> _low; // Low-link values
    private Stack<T> _stack; // Stack for Tarjan's
    private HashSet<T> _onStack; // Nodes currently on stack
    private List<HashSet<T>> _sccs; // List of SCCs
    private Dictionary<T, int> _sccIndex; // Node to SCC index mapping
    private Dictionary<int, HashSet<int>> _dag; // DAG of SCCs
    private Dictionary<int, HashSet<T>> _closure; // Transitive closure per SCC

    public void AddNode(T u)
    {
        if (!_adj.ContainsKey(u))
            _adj[u] = new HashSet<T>();
    }

    public void AddEdge(T u, T v)
    {
        AddNode(u);
        AddNode(v);
        _adj[u].Add(v);
    }

    public void ComputeTransitiveClosureInPlace()
    {
        FindSCCs(); // Step 1: Identify SCCs
        BuildDAG(); // Step 2: Construct DAG of SCCs
        ComputeClosure(); // Step 3: Compute transitive closure on DAG
        AugmentAdjacency(); // Step 4: Update original adjacency lists
    }

    private void FindSCCs()
    {
        _disc = new Dictionary<T, int>();
        _low = new Dictionary<T, int>();
        _stack = new Stack<T>();
        _onStack = new HashSet<T>();
        _sccs = new List<HashSet<T>>();
        _sccIndex = new Dictionary<T, int>();

        foreach (var u in _adj.Keys)
        {
            if (!_disc.ContainsKey(u))
                TarjanDFS(u);
        }
    }

    private void TarjanDFS(T u)
    {
        _disc[u] = _low[u] = _time++;
        _stack.Push(u);
        _onStack.Add(u);

        foreach (var v in _adj[u])
        {
            if (!_disc.TryGetValue(v, out var value)) // Not visited
            {
                TarjanDFS(v);
                _low[u] = Math.Min(_low[u], _low[v]);
            }
            else if (_onStack.Contains(v)) // Back edge to node on stack
            {
                _low[u] = Math.Min(_low[u], value);
            }
        }

        if (_low[u] == _disc[u]) // u is the root of an SCC
        {
            var scc = new HashSet<T>();
            while (true)
            {
                var v = _stack.Pop();
                _onStack.Remove(v);
                scc.Add(v);
                _sccIndex[v] = _sccs.Count;
                if (v.Equals(u)) break;
            }

            _sccs.Add(scc);
        }
    }

    private void BuildDAG()
    {
        _dag = new Dictionary<int, HashSet<int>>();
        for (int i = 0; i < _sccs.Count; i++)
            _dag[i] = new HashSet<int>();

        foreach (var u in _adj.Keys)
        {
            int sccU = _sccIndex[u];
            foreach (var v in _adj[u])
            {
                int sccV = _sccIndex[v];
                if (sccU != sccV)
                    _dag[sccU].Add(sccV);
            }
        }
    }

    private void ComputeClosure()
    {
        var topo = TopologicalSort();
        _closure = new Dictionary<int, HashSet<T>>();

        for (int i = topo.Count - 1; i >= 0; i--)
        {
            int scc = topo[i];
            var reach = new HashSet<T>(_sccs[scc]); // Include all nodes in this SCC
            foreach (var nextScc in _dag[scc])
            {
                reach.UnionWith(_closure[nextScc]); // Union with successors' closures
            }

            _closure[scc] = reach;
        }
    }

    private List<int> TopologicalSort()
    {
        var indegree = new Dictionary<int, int>();
        for (int i = 0; i < _sccs.Count; i++)
            indegree[i] = 0;

        foreach (var scc in _dag.Keys)
        foreach (var nextScc in _dag[scc])
            indegree[nextScc] = indegree.GetValueOrDefault(nextScc, 0) + 1;

        var q = new Queue<int>();
        for (int i = 0; i < _sccs.Count; i++)
            if (indegree[i] == 0)
                q.Enqueue(i);

        var topo = new List<int>();
        while (q.Count > 0)
        {
            var scc = q.Dequeue();
            topo.Add(scc);
            foreach (var nextScc in _dag[scc])
            {
                indegree[nextScc]--;
                if (indegree[nextScc] == 0)
                    q.Enqueue(nextScc);
            }
        }

        return topo;
    }

    private void AugmentAdjacency()
    {
        foreach (var u in _adj.Keys.ToList())
        {
            int scc = _sccIndex[u];
            _adj[u].UnionWith(_closure[scc]); // Augment with SCC's transitive closure
        }
    }

    public bool IsReachable(T u, T v)
    {
        if (!_adj.TryGetValue(u, out var reachable))
            throw new InvalidOperationException("Unknown node: " + u);
        return reachable.Contains(v);
    }
}
//
// public class Digraph<T>
// {
//     // adjacency list, using hash‐sets so we can union in place without dupes
//     private readonly Dictionary<T, HashSet<T>> _adj = new();
//
//     /// <summary>
//     /// Add a node (if not already present).
//     /// </summary>
//     public void AddNode(T u)
//     {
//         if (!_adj.ContainsKey(u))
//             _adj[u] = new HashSet<T>();
//     }
//
//     /// <summary>
//     /// Add a directed edge u → v. Automatically adds u and v as nodes if needed.
//     /// </summary>
//     public void AddEdge(T u, T v)
//     {
//         AddNode(u);
//         AddNode(v);
//         _adj[u].Add(v);
//     }
//
//     /// <summary>
//     /// Computes the transitive closure by augmenting the existing adjacency sets.
//     /// After calling this, _adj[u] contains all original successors of u _and_ all
//     /// nodes reachable via any path from u.
//     /// </summary>
//     public void ComputeTransitiveClosureInPlace()
//     {
//         // 1. Topological sort (Kahn's algorithm)
//         var indegree = _adj.Keys.ToDictionary(u => u, _ => 0);
//         foreach (var u in _adj.Keys)
//             foreach (var v in _adj[u])
//                 indegree[v] = indegree.GetValueOrDefault(v) + 1;
//
//         var q = new Queue<T>(indegree.Where(kv => kv.Value == 0).Select(kv => kv.Key));
//         var topo = new List<T>();
//         while (q.Count > 0)
//         {
//             var u = q.Dequeue();
//             topo.Add(u);
//             foreach (var v in _adj[u])
//             {
//                 indegree[v]--;
//                 if (indegree[v] == 0)
//                     q.Enqueue(v);
//             }
//         }
//
//         // 2. Compute closures locally
//         var closure = new Dictionary<T, HashSet<T>>();
//         foreach (var u in topo.AsEnumerable().Reverse())
//         {
//             var reach = new HashSet<T>();
//             foreach (var v in _adj[u])
//             {
//                 reach.Add(v);                             // direct edge
//                 if (closure.TryGetValue(v, out var vr))   // plus everything v can reach
//                     reach.UnionWith(vr);
//             }
//             closure[u] = reach;
//         }
//
//         // 3. Augment the original adjacency sets in place
//         foreach (var u in closure.Keys.ToList())
//         {
//             _adj[u].UnionWith(closure[u]);
//         }
//     }
//
//     /// <summary>
//     /// Returns true iff there is a path u →* v in the graph.
//     /// ComputeTransitiveClosureInPlace() must have been called first.
//     /// </summary>
//     public bool IsReachable(T u, T v)
//     {
//         if (!_adj.TryGetValue(u, out var value))
//             throw new InvalidOperationException("Unknown node: " + u);
//         return value.Contains(v);
//     }
// }