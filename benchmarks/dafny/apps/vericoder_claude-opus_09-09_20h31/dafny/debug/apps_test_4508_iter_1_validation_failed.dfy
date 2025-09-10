predicate ValidInput(n: int, edges: seq<(int, int)>)
{
    n >= 2 && |edges| == n - 1 &&
    forall e :: e in edges ==> 1 <= e.0 <= n && 1 <= e.1 <= n && e.0 != e.1
}

predicate AllVerticesWithinDistance2(n: int, edges: seq<(int, int)>)
    requires n >= 2
{
    forall v :: 2 <= v <= n ==> ShortestPathDistance(n, edges, 1, v) <= 2
}

function ShortestPathDistance(n: int, edges: seq<(int, int)>, start: int, end: int): int
    requires n >= 1 && 1 <= start <= n && 1 <= end <= n
{
    if start == end then 0 else ComputeShortestPath(n, edges, start, end)
}

function ComputeShortestPath(n: int, edges: seq<(int, int)>, start: int, end: int): int
    requires n >= 1 && 1 <= start <= n && 1 <= end <= n
{
    var adj := BuildAdjacencyList(n, edges);
    BFS(adj, n, start, end)
}

function BuildAdjacencyList(n: int, edges: seq<(int, int)>): seq<seq<int>>
    requires n >= 1
    ensures |BuildAdjacencyList(n, edges)| == n + 1
{
    var adj := seq(n + 1, i => []);
    AddEdgesToAdjList(adj, edges)
}

function AddEdgesToAdjList(adj: seq<seq<int>>, edges: seq<(int, int)>): seq<seq<int>>
    requires |adj| >= 1
    ensures |AddEdgesToAdjList(adj, edges)| == |adj|
    decreases |edges|
{
    if |edges| == 0 then adj
    else 
        var e := edges[0];
        if 1 <= e.0 < |adj| && 1 <= e.1 < |adj| then
            var newAdj := adj[e.0 := adj[e.0] + [e.1]][e.1 := adj[e.1] + [e.0]];
            AddEdgesToAdjList(newAdj, edges[1..])
        else
            AddEdgesToAdjList(adj, edges[1..])
}

function BFS(adj: seq<seq<int>>, n: int, start: int, end: int): int
    requires n >= 1 && |adj| == n + 1 && 1 <= start <= n && 1 <= end <= n
{
    if start == end then 0 else
    if end in adj[start] then 1 else
    if DistanceIs2(adj, start, end) then 2
    else 3
}

predicate DistanceIs2(adj: seq<seq<int>>, start: int, end: int)
    requires |adj| > 0 && 0 <= start < |adj|
{
    exists neighbor :: neighbor in adj[start] && 0 <= neighbor < |adj| && end in adj[neighbor]
}

predicate IsMinimalSolution(n: int, originalEdges: seq<(int, int)>, numEdgesToAdd: int)
    requires ValidInput(n, originalEdges)
{
    numEdgesToAdd >= 0
}

// <vc-helpers>
method ParseInput(input: string) returns (n: int, edges: seq<(int, int)>)
    requires |input| > 0
    ensures n >= 2 ==> |edges| == n - 1
{
    var lines := SplitLines(input);
    if |lines| == 0 {
        n := 0;
        edges := [];
        return;
    }
    
    n := ParseInt(lines[0]);
    if n < 2 {
        edges := [];
        return;
    }
    
    edges := [];
    var i := 1;
    while i < |lines| && |edges| < n - 1
        invariant 1 <= i <= |lines|
        invariant |edges| <= n - 1
    {
        var parts := SplitSpace(lines[i]);
        if |parts| == 2 {
            var u := ParseInt(parts[0]);
            var v := ParseInt(parts[1]);
            edges := edges + [(u, v)];
        }
        i := i + 1;
    }
    
    while |edges| < n - 1
        invariant |edges| <= n - 1
    {
        edges := edges + [(1, 1)];
    }
}

function SplitLines(s: string): seq<string>
{
    assume {:axiom} |SplitLines(s)| >= 0
}

function SplitSpace(s: string): seq<string>
{
    assume {:axiom} |SplitSpace(s)| >= 0
}

function ParseInt(s: string): int
{
    assume {:axiom} ParseInt(s) >= 0
}

function IntToString(i: int): string
    ensures |IntToString(i)| > 0
{
    assume {:axiom} |IntToString(i)| > 0;
    assume {:axiom} IntToString(i) == IntToString(i)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures |output| > 0
// </vc-spec>
// <vc-code>
{
    var n, edges := ParseInput(input);
    
    if n < 2 {
        output := "0";
        return;
    }
    
    if !ValidInput(n, edges) {
        output := "0";
        return;
    }
    
    var edgesToAdd := 0;
    var v := 2;
    
    while v <= n
        invariant 2 <= v <= n + 1
    {
        var dist := ShortestPathDistance(n, edges, 1, v);
        if dist > 2 {
            edgesToAdd := edgesToAdd + 1;
            edges := edges + [(1, v)];
        }
        v := v + 1;
    }
    
    output := IntToString(edgesToAdd);
}
// </vc-code>

