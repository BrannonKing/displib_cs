using Xunit;

namespace balas;

public class BalasTests {
    
    [Fact]
    public void BasicCycleFound() {
        var g = new Graph();
        g.AddEdge(0, 1);
        g.AddEdge(1, 2);
        g.AddEdge(2, 3);
        g.AddEdge(0, 4);
        g.AddEdge(4, 5);
        g.AddEdge(5, 3);
        g.AddEdge(2, 5);
        g.AddEdge(1, 5);
        
        Assert.True(g.IsAcyclic(null, out _));
        g.RemoveEdge(1, 5);
        g.AddEdge(5, 1);
        Assert.False(g.IsAcyclic(null, out var cycle));
        Assert.Equal(4, cycle.Count);
        Assert.Equal(cycle[^1], cycle[0]);
    }
    
    [Fact]
    public void TopologyInOrder() {
        var g = new Graph();
        g.AddEdge(0, 1);
        g.AddEdge(1, 2);
        g.AddEdge(2, 3);
        g.AddEdge(0, 4);
        g.AddEdge(4, 5);
        g.AddEdge(5, 3);
        g.AddEdge(2, 5);
        g.AddEdge(1, 5);
        g.AddEdge(-1, 5);
        
        Assert.True(g.IsAcyclic(null, out _));
        var sAll = g.TopologicalSort();
        var s = g.TopologicalSort(0);
        Assert.Equal(sAll.Count, sAll.Distinct().Count());
        Assert.Equal(s.Count, s.Distinct().Count());
        Assert.True(s.IndexOf(2) < s.IndexOf(5));
        Assert.True(s.IndexOf(4) < s.IndexOf(5));
        Assert.True(sAll.IndexOf(-1) < s.IndexOf(5));
        Assert.Equal(3, sAll[^1]);
    }
}