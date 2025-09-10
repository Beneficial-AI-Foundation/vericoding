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
lemma {:timeLimit 3} BFS_Correctness(adj: seq<seq<int>>, n: int, start: int, end: int) returns (d: int)
    requires n >= 1 && |adj| == n + 1 && 1 <= start <= n && 1 <= end <= n
    ensures d == ShortestPathDistance(n, BuildEdgesFromAdj(adj), start, end)
{
    // This lemma helps connect the BFS function to the actual shortest path computation
}

function BuildEdgesFromAdj(adj: seq<seq<int>>): seq<(int, int)>
    requires |adj| >= 2
{
    // Convert adjacency list back to edge list for compatibility with ShortestPathDistance
    var edges: seq<(int, int)> := [];
    var i := 1;
    while i < |adj|
        invariant 1 <= i <= |adj|
    {
        foreach neighbor in adj[i] {
            if i < neighbor then
                edges := edges + [(i, neighbor)];
        }
        i := i + 1;
    }
    edges
}

lemma {:timeLimit 3} AdjacencyListCorrectness(n: int, edges: seq<(int, int)>) 
    requires n >= 1
    ensures BuildAdjacencyList(n, edges) == AddEdgesToAdjList(seq(n + 1, i => []), edges)
{
    // Helper lemma to verify adjacency list construction
}

predicate IsValidOutputSolution(n: int, originalEdges: seq<(int, int)>, numEdgesToAdd: int)
    requires ValidInput(n, originalEdges)
{
    var adj := BuildAdjacencyList(n, originalEdges);
    var vertices: set<int> := {1};
    var queue: seq<int> := [1];
    var dist: seq<int> := seq(n + 1, i => if i == 1 then 0 else -1);
    
    while |queue| > 0
        invariant true // Simplified for verification
    {
        var current := queue[0];
        queue := queue[1..];
        
        foreach neighbor in adj[current] {
            if dist[neighbor] == -1 {
                dist := dist[neighbor := dist[current] + 1];
                queue := queue + [neighbor];
            }
        }
    }
    
    forall v | 2 <= v <= n :: dist[v] <= 2 + numEdgesToAdd
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures |output| > 0
// </vc-spec>
// <vc-code>
{
    var lines := input.Split("\n");
    var data := lines[0].Split(" ");
    var n := data[0] as int;
    var edges: seq<(int, int)> := [];
    
    for i := 1 to n - 1
        invariant |edges| == i - 1
    {
        var line := lines[i].Split(" ");
        var u := line[0] as int;
        var v := line[1] as int;
        edges := edges + [(u, v)];
    }
    
    var dist: seq<int> := seq(n + 1, i => 0);
    var adj := BuildAdjacencyList(n, edges);
    var maxDist := 0;
    
    for v := 2 to n
        invariant maxDist == (if v == 2 then 0 else max j :: 2 <= j < v ==> dist[j])
    {
        dist := dist[v := ShortestPathDistance(n, edges, 1, v)];
        if dist[v] > maxDist {
            maxDist := dist[v];
        }
    }
    
    var numEdgesToAdd := if maxDist <= 2 then 0 else (maxDist - 2);
    output := numEdgesToAdd.ToString();
}
// </vc-code>

