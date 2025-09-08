Given n points and m segments, find a "hedgehog" with maximum beauty.
A hedgehog has a tail (path with strictly increasing point numbers) and 
spines (all segments connected to tail's endpoint). 
Beauty = (tail length) × (number of spines).

predicate ValidInput(n: int, edges: seq<(int, int)>)
{
    n >= 2 &&
    forall i :: 0 <= i < |edges| ==> 1 <= edges[i].0 <= n && 1 <= edges[i].1 <= n && edges[i].0 != edges[i].1
}

predicate ValidOutput(result: int, n: int, edges: seq<(int, int)>)
{
    result >= 0 && result <= 2 * |edges| * (|edges| + 1)
}

method SortEdges(edges: seq<(int, int)>) returns (sorted: seq<(int, int)>)
    ensures |sorted| == |edges|
    ensures multiset(sorted) == multiset(edges)
{
    sorted := edges;
    var i := 0;
    while i < |sorted|
        invariant 0 <= i <= |sorted|
        invariant |sorted| == |edges|
        invariant multiset(sorted) == multiset(edges)
    {
        var j := 0;
        while j < |sorted| - 1 - i
            invariant 0 <= j <= |sorted| - 1 - i
            invariant |sorted| == |edges|
            invariant multiset(sorted) == multiset(edges)
        {
            if sorted[j].0 > sorted[j + 1].0 || (sorted[j].0 == sorted[j + 1].0 && sorted[j].1 > sorted[j + 1].1) {
                var temp := sorted[j];
                sorted := sorted[j := sorted[j + 1]][j + 1 := temp];
            }
            j := j + 1;
        }
        i := i + 1;
    }
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

function max(a: int, b: int): int
{
    if a >= b then a else b
}

method solve(n: int, edges: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, edges)
    ensures ValidOutput(result, n, edges)
{
    if |edges| == 0 {
        result := 0;
        return;
    }

    // Count connections for each vertex (potential spines)
    var connections := seq(n, i => 0);
    var i := 0;
    while i < |edges|
        invariant 0 <= i <= |edges|
        invariant |connections| == n
        invariant forall k :: 0 <= k < n ==> connections[k] >= 0
        invariant forall k :: 0 <= k < n ==> connections[k] <= 2 * i
    {
        var u := edges[i].0 - 1;
        var v := edges[i].1 - 1;
        connections := connections[u := connections[u] + 1];
        connections := connections[v := connections[v] + 1];
        i := i + 1;
    }

    // Create normalized edges (min, max) and sort them
    var normalizedEdges := seq(|edges|, i requires 0 <= i < |edges| => (min(edges[i].0, edges[i].1), max(edges[i].0, edges[i].1)));
    var sortedEdges := SortEdges(normalizedEdges);

    // Dynamic programming: dp[i] = longest increasing path ending at vertex i+1
    var dp := seq(n, i => 1);
    var edgeIdx := 0;
    while edgeIdx < |sortedEdges|
        invariant 0 <= edgeIdx <= |sortedEdges|
        invariant |dp| == n
        invariant forall i :: 0 <= i < n ==> dp[i] >= 1
        invariant forall i :: 0 <= i < n ==> dp[i] <= edgeIdx + 1
    {
        var edge := sortedEdges[edgeIdx];
        var u := edge.0 - 1;  // Convert to 0-based indexing
        var v := edge.1 - 1;  // Convert to 0-based indexing
        if 0 <= u < n && 0 <= v < n {
            dp := dp[v := max(dp[v], dp[u] + 1)];
        }
        edgeIdx := edgeIdx + 1;
    }

    // Find maximum beauty = max(dp[i] * connections[i])
    result := 0;
    var j := 0;
    while j < n
        invariant 0 <= j <= n
        invariant result >= 0
        invariant result <= 2 * |edges| * (|edges| + 1)
    {
        var beauty := dp[j] * connections[j];
        if beauty > result {
            result := beauty;
        }
        j := j + 1;
    }
}
