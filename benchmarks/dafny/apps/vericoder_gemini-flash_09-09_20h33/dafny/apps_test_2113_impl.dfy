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

// <vc-helpers>
predicate {:opaque} IsBipartite(n: int, edges: seq<(int, int)>, colors: array<int>)
    requires n > 0 && colors.Length == n
{
    (forall i :: 0 <= i < n ==> (colors[i] == 0 || colors[i] == 1)) && // All nodes are colored
    (forall i :: 0 <= i < |edges| ==>
        var u := edges[i].0;
        var v := edges[i].1;
        1 <= u <= n && 1 <= v <= n && colors[u-1] != colors[v-1])
}

method {:opaque} BFS(n: int, edges: seq<(int, int)>, startNode: int, colors: array<int>) returns (isBipartite: bool)
    requires n > 0 && colors.Length == n
    requires 1 <= startNode <= n
    requires forall i :: 0 <= i < n ==> colors[i] == -1
    ensures isBipartite ==> IsBipartite(n, edges, colors)
    ensures (forall i :: 0 <= i < n ==> colors[i] == -1 || colors[i] == 0 || colors[i] == 1)
{
    var q := new seq<int>[0];
    q := q + [startNode];
    colors[startNode - 1] := 0; // Color start node with 0 (e.g., blue)
    var head := 0;

    isBipartite := true;

    while head < |q|
        invariant isBipartite
        invariant head <= |q|
        invariant forall i :: 0 <= i < n ==> colors[i] == -1 || colors[i] == 0 || colors[i] == 1
        invariant forall i :: 0 <= i < head ==> colors[q[i]-1] != -1
        invariant forall i :: head <= i < |q| ==> colors[q[i]-1] != -1 // All nodes in queue are colored
        invariant forall i, j :: 0 <= i < j < |q| ==> q[i] != q[j] // Queue contains distinct nodes
        invariant forall u :: 1 <= u <= n && colors[u-1] != -1 ==> (exists k :: 0 <= k < |q| && q[k] == u && colors[u-1] != -1) || (exists k :: 0 <= k < head && q[k] == u && colors[u-1] != -1)
        invariant forall u, v :: 1 <= u <= n && 1 <= v <= n && colors[u-1] != -1 && colors[v-1] != -1 && (exists k :: 0 <= k < |edges| && ((edges[k].0 == u && edges[k].1 == v) || (edges[k].0 == v && edges[k].1 == u))) ==> colors[u-1] != colors[v-1]
        invariant forall k :: 0 <= k < |edges| ==> 1 <= edges[k].0 <= n && 1 <= edges[k].1 <= n
    {
        var u := q[head];
        head := head + 1;

        for i := 0 to |edges| - 1
            invariant isBipartite
            invariant head <= |q|
            invariant forall k :: 0 <= k < head ==> colors[q[k]-1] != -1
            invariant forall k :: head <= k < |q| ==> colors[q[k]-1] != -1
            invariant forall s, t :: 0 <= s < t < |q| ==> q[s] != q[t]
            invariant forall x :: 1 <= x <= n && colors[x-1] != -1 ==> (exists k :: 0 <= k < |q| && q[k] == x && colors[x-1] != -1) || (exists k :: 0 <= k < head && q[k] == x && colors[x-1] != -1)
            invariant forall x :: 0 <= x < n ==> colors[x] == -1 || colors[x] == 0 || colors[x] == 1
            invariant forall x, y :: 1 <= x <= n && 1 <= y <= n && colors[x-1] != -1 && colors[y-1] != -1 && (exists k :: 0 <= k < |edges| && ((edges[k].0 == x && edges[k].1 == y) || (edges[k].0 == y && edges[k].1 == x))) ==> colors[x-1] != colors[y-1]
            invariant forall k :: 0 <= k < |edges| ==> 1 <= edges[k].0 <= n && 1 <= edges[k].1 <= n
        {
            var v_node: int;
            if edges[i].0 == u {
                v_node := edges[i].1;
            } else if edges[i].1 == u {
                v_node := edges[i].0;
            } else {
                continue;
            }

            // By ValidTreeInput, 1 <= edges[i].0 <= n and 1 <= edges[i].1 <= n
            // So 1 <= u <= n and 1 <= v_node <= n
            // Thus, 0 <= u - 1 < n and 0 <= v_node - 1 < n
            
            if colors[v_node - 1] == -1 {
                // Assign opposite color
                colors[v_node - 1] := 1 - colors[u - 1]; 
                q := q + [v_node];
            } else if colors[v_node - 1] == colors[u - 1] {
                isBipartite := false; // Found an edge with same-colored endpoints
            }
        }
    }
    return isBipartite;
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    if n == 1 || n == 2 {
        return 0;
    }

    // Initialize colors array with -1 (uncolored)
    var colors := new int[n];
    for i := 0 to n - 1 {
        colors[i] := -1;
    }

    // Check if the graph is bipartite using BFS
    // Since it's a connected tree, we only need to run BFS once starting from node 1.
    // The proof that a tree is always bipartite means isBipartite will always be true.
    var isBipartite := BFS(n, edges, 1, colors);

    // If the graph is bipartite (which it always is for a tree), count blue and red nodes
    var blue_count := 0;
    var red_count := 0;
    for i := 0 to n - 1 {
        // Since isBipartite is true and BFS ensures all reachable nodes are colored,
        // and a tree is connected, all nodes will be colored 0 or 1.
        if colors[i] == 0 {
            blue_count := blue_count + 1;
        } else { // colors[i] must be 1
            red_count := red_count + 1;
        }
    }
    return blue_count * red_count - (n - 1);
}
// </vc-code>

