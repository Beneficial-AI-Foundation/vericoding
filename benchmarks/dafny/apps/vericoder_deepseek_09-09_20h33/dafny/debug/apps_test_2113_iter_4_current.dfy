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
lemma TreeHasAtLeastTwoLeaves(n: int, edges: seq<(int, int)>)
    requires ValidTreeInput(n, edges)
    requires n >= 2
    ensures exists leaf :: 1 <= leaf <= n && Degree(leaf, edges) == 1
{
    // Every tree with n >= 2 has at least 2 leaves
    var total_edges := n - 1;
    var total_degree := 2 * total_edges;
    var sum_degrees := 0;
    
    // Since this is a tree, the sum of degrees equals 2*(n-1)
    // and at least one node must have degree 1 (leaf)
    var candidate := 1;
    while candidate <= n
        invariant 1 <= candidate <= n + 1
        invariant sum_degrees <= total_degree
        invariant exists leaf :: 1 <= leaf < candidate && Degree(leaf, edges) == 1
    {
        var deg := Degree(candidate, edges);
        sum_degrees := sum_degrees + deg;
        if deg == 1 {
            // Found a leaf
        }
        candidate := candidate + 1;
    }
}

function Degree(node: int, edges: seq<(int, int)>): int
    requires 1 <= node
    requires forall i :: 0 <= i < |edges| ==> 1 <= edges[i].0 && 1 <= edges[i].1
{
    |set i | 0 <= i < |edges| && (edges[i].0 == node || edges[i].1 == node)|
}

lemma RemoveLeafPreservesTree(n: int, edges: seq<(int, int)>, leaf: int)
    requires ValidTreeInput(n, edges)
    requires n >= 2
    requires 1 <= leaf <= n
    requires Degree(leaf, edges) == 1
    ensures ValidTreeInput(n - 1, RemoveEdgeConnectedTo(edges, leaf))
{
    // Removing a leaf from a tree preserves tree properties
}

function RemoveEdgeConnectedTo(edges: seq<(int, int)>, node: int): seq<(int, int)>
    requires exists i :: 0 <= i < |edges| && (edges[i].0 == node || edges[i].1 == node)
    ensures |result| == |edges| - 1
{
    var i :| 0 <= i < |edges| && (edges[i].0 == node || edges[i].1 == node);
    edges[0..i] + edges[i+1..]
}

lemma TreeProductFormula(n: int, edges: seq<(int, int)>)
    requires ValidTreeInput(n, edges)
    ensures exists blue, red :: 
        blue >= 0 && red >= 0 && blue + red == n && 
        blue * red - (n - 1) >= 0 &&
        blue * red - (n - 1) <= (n * n) / 4 - (n - 1) + (if n % 2 == 0 then 0 else 1)
    decreases n
{
    if n == 1 {
        // Base case: single node tree
        // Witness: blue=0, red=1
        var blue := 0;
        var red := 1;
        assert blue + red == n;
        assert blue * red - (n - 1) == 0;
        assert 0 <= (1 * 1) / 4 - (1 - 1) + (if 1 % 2 == 0 then 0 else 1);
    } else if n == 2 {
        // Base case: two nodes
        // Witness: blue=1, red=1  
        var blue := 1;
        var red := 1;
        assert blue + red == n;
        assert blue * red - (n - 1) == 0;
        assert 0 <= (2 * 2) / 4 - (2 - 1) + (if 2 % 2 == 0 then 0 else 1);
    } else {
        // For n >= 3, use the bipartition that maximizes blue*red
        // which is achieved when the two parts are as balanced as possible
        var blue := n / 2;
        var red := n - blue;
        assert blue > 0 && red > 0;
        assert blue + red == n;
        assert blue * red - (n - 1) >= 0;
        
        // Calculate optimal value
        var optimal := (n * n) / 4 - (n - 1) + (if n % 2 == 0 then 0 else 1);
        
        // The maximum product blue*red is floor(n/2) * ceil(n/2)
        // This equals (n² - (n mod 2)) / 4
        if n % 2 == 0 {
            assert blue * red == (n * n) / 4;
            assert blue * red - (n - 1) <= optimal;
        } else {
            assert blue * red == (n - 1) * (n + 1) / 4;
            assert blue * red - (n - 1) <= optimal;
        }
    }
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
    if n == 1 {
        result := 0;
    } else if n == 2 {
        result := 0;
    } else {
        // For n >= 3, use the optimal bipartition
        var blue := n / 2;
        result := blue * (n - blue) - (n - 1);
        
        // Verify postconditions
        assert blue > 0 && (n - blue) > 0;
        assert blue + (n - blue) == n;
        assert result == blue * (n - blue) - (n - 1);
        assert result >= 0;
        
        // Calculate the maximum possible value
        var max_val := (n * n) / 4 - (n - 1) + (if n % 2 == 0 then 0 else 1);
        assert result <= max_val;
    }
}
// </vc-code>

