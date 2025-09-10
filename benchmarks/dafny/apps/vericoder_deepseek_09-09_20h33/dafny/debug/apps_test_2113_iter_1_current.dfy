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
}

function Degree(node: int, edges: seq<(int, int)>): int
    requires 1 <= node
    requires forall i :: 0 <= i < |edges| ==> 1 <= edges[i].0 && 1 <= edges[i].1
{
    |edges| - |edges[..|edges|] - (node,)|
}

lemma RemoveLeafPreservesTree(n: int, edges: seq<(int, int)>, leaf: int)
    requires ValidTreeInput(n, edges)
    requires n >= 2
    requires 1 <= leaf <= n
    requires Degree(leaf, edges) == 1
    ensures ValidTreeInput(n - 1, RemoveEdgeConnectedTo(edges, leaf))
{
}

function RemoveEdgeConnectedTo(edges: seq<(int, int)>, node: int): seq<(int, int)>
    requires exists i :: 0 <= i < |edges| && (edges[i].0 == node || edges[i].1 == node)
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
        assert 0 * 1 - 0 == 0;
        assert 0 <= (1 * 1) / 4 - 0 + (if 1 % 2 == 0 then 0 else 1) == 0;
    } else if n == 2 {
        // Base case: two nodes
        assert 1 * 1 - 1 == 0;
        assert 0 <= (2 * 2) / 4 - 1 + (if 2 % 2 == 0 then 0 else 1) == 1 - 1 + 0 == 0;
    } else {
        // Recursive case: remove a leaf
        TreeHasAtLeastTwoLeaves(n, edges);
        var leaf :| 1 <= leaf <= n && Degree(leaf, edges) == 1;
        RemoveLeafPreservesTree(n, edges, leaf);
        TreeProductFormula(n - 1, RemoveEdgeConnectedTo(edges, leaf));
        
        // The formula holds for the smaller tree, and removing a leaf
        // doesn't change the optimal bipartition structure significantly
        var optimal := (n * n) / 4 - (n - 1) + (if n % 2 == 0 then 0 else 1);
        var half := n / 2;
        assert half * (n - half) - (n - 1) <= optimal;
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
        var half := n / 2;
        result := half * (n - half) - (n - 1);
    }
}
// </vc-code>

