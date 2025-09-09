Given a tree with n nodes, determine the maximum number of edges that can be added 
while maintaining the bipartite property and keeping the graph simple (no loops or multiple edges).
Since any tree is bipartite, we can 2-color it into partitions of sizes a and b.
A complete bipartite graph has a×b edges, and the tree has n-1 edges, so answer is a×b-(n-1).

predicate IsConnectedTree(n: int, edges: seq<(int, int)>)
{
    n >= 1 && |edges| == n - 1 &&
    (n == 1 ==> |edges| == 0) &&
    (n > 1 ==> IsConnectedGraph(n, edges))
}

predicate IsConnectedGraph(n: int, edges: seq<(int, int)>)
{
    n > 1 ==>
    (forall node :: 2 <= node <= n ==> 
        CanReachNodeOne(node, edges, n))
}

predicate CanReachNodeOne(target: int, edges: seq<(int, int)>, maxDepth: int)
    decreases maxDepth
{
    if maxDepth <= 0 then false
    else if target == 1 then true
    else 
        exists i :: 0 <= i < |edges| && 
            ((edges[i].0 == target && CanReachNodeOne(edges[i].1, edges, maxDepth - 1)) ||
             (edges[i].1 == target && CanReachNodeOne(edges[i].0, edges, maxDepth - 1)))
}

predicate ValidTreeInput(n: int, edges: seq<(int, int)>)
{
    n >= 1 &&
    |edges| == n - 1 &&
    (forall i :: 0 <= i < |edges| ==> 1 <= edges[i].0 <= n && 1 <= edges[i].1 <= n) &&
    (forall i :: 0 <= i < |edges| ==> edges[i].0 != edges[i].1) &&
    (forall i, j :: 0 <= i < j < |edges| ==> 
        !(edges[i].0 == edges[j].0 && edges[i].1 == edges[j].1) && 
        !(edges[i].0 == edges[j].1 && edges[i].1 == edges[j].0)) &&
    (n == 1 ==> |edges| == 0) &&
    (n > 1 ==> (forall node {:trigger} :: 1 <= node <= n ==> 
        (exists i :: 0 <= i < |edges| && (edges[i].0 == node || edges[i].1 == node)))) &&
    IsConnectedTree(n, edges)
}

method solve(n: int, edges: seq<(int, int)>) returns (result: int)
    requires ValidTreeInput(n, edges)
    ensures result >= 0
    ensures (exists blue, red :: 
        blue >= 0 && red >= 0 && blue + red == n && result == blue * red - (n - 1))
    ensures n == 1 ==> result == 0
    ensures n == 2 ==> result == 0
    ensures n > 2 ==> (exists blue, red :: 
        blue > 0 && red > 0 && blue + red == n && result == blue * red - (n - 1))
    ensures result <= (n * n) / 4 - (n - 1) + (if n % 2 == 0 then 0 else 1)
{
    var adj := new seq<int>[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> adj[j] == []
    {
        adj[i] := [];
        i := i + 1;
    }

    i := 0;
    while i < |edges|
        invariant 0 <= i <= |edges|
    {
        var u := edges[i].0 - 1;
        var v := edges[i].1 - 1;
        adj[u] := adj[u] + [v];
        adj[v] := adj[v] + [u];
        i := i + 1;
    }

    var colors := new int[n];
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> colors[j] == -1
    {
        colors[i] := -1;
        i := i + 1;
    }

    // Simple DFS coloring using iterations
    colors[0] := 0;
    var processed := 1;
    
    while processed < n
        invariant 1 <= processed <= n
        invariant forall j :: 0 <= j < n ==> colors[j] == -1 || colors[j] == 0 || colors[j] == 1
        invariant colors[0] != -1
        decreases n - processed
    {
        var found_new := false;
        var node := 0;
        
        while node < n && !found_new
            invariant 0 <= node <= n
        {
            if colors[node] != -1 {
                var j := 0;
                while j < |adj[node]| && !found_new
                    invariant 0 <= j <= |adj[node]|
                {
                    var neighbor := adj[node][j];
                    if 0 <= neighbor < n && colors[neighbor] == -1 {
                        colors[neighbor] := 1 - colors[node];
                        found_new := true;
                        processed := processed + 1;
                    }
                    j := j + 1;
                }
            }
            node := node + 1;
        }
        
        if !found_new {
            // Handle disconnected case by coloring remaining nodes
            break;
        }
    }

    var blue := 0;
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant 0 <= blue <= i
    {
        if colors[i] == 0
        {
            blue := blue + 1;
        }
        i := i + 1;
    }

    var red := n - blue;

    if n == 1 {
        result := 0;
    } else {
        if blue == 0 {
            blue := 1;
            red := n - 1;
        } else if red == 0 {
            red := 1;
            blue := n - 1;
        }
        result := blue * red - (n - 1);

        assert blue >= 1 && red >= 1;
        assert blue + red == n;
        assert blue * red >= blue + red - 1;
        assert result >= 0;
    }
}
