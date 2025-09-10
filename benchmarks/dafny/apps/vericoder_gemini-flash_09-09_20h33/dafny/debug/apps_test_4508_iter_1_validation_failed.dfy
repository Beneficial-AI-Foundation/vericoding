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
predicate IsConnectedGraph(n: int, edges: seq<(int, int)>)
    requires n >= 1
{
    var adj := BuildAdjacencyList(n, edges);
    forall v :: 1 <= v <= n ==> BFS(adj, n, 1, v) < n // Any path length less than n implies connectivity
}

predicate IsTree(n: int, edges: seq<(int, int)>)
    requires ValidInput(n, edges)
{
    IsConnectedGraph(n, edges)
}

function IsStarGraph(n: int, edges: seq<(int, int)>): bool
    requires n >= 2
    requires ValidInput(n, edges)
{
    exists center :: 1 <= center <= n &&
    (forall e :: e in edges ==> (e.0 == center || e.1 == center))
}

function AllVerticesWithinDistanceD(n: int, edges: seq<(int, int)>, startNode: int, d: int): bool
    requires n >= 1 && 1 <= startNode <= n && d >= 0
{
    forall v :: 1 <= v <= n && v != startNode ==> ShortestPathDistance(n, edges, startNode, v) <= d
}

// Function to convert string to int, assuming valid int format
function StringToInt(s: string): int
    reads s
    ensures StringToInt(s) >= 0
{
    var i := 0;
    var res := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant res >= 0
        invariant forall k :: 0 <= k < i ==> '0' <= s[k] <= '9'
    {
        res := res * 10 + (s[i] - '0');
        i := i + 1;
    }
    res
}

// Function to convert int to string
function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else
        var s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant s == IntToStringReverse(n, temp)
        {
            var digit := temp % 10;
            s := "" + (char)(digit + '0') + s;
            temp := temp / 10;
        }
        s
}

// Helper for IntToString, reversing the string
function IntToStringReverse(n: int, temp: int): string
    requires n >= 0 && temp >= 0
    decreases temp
{
    if temp == 0 then ""
    else IntToStringReverse(n, temp / 10) + (char)(temp % 10 + '0')
}

// Function to parse the input string and extract n and edges
// This is a simplified parser and assumes input format "n m e1 e2 ... em" where m=n-1
function ParseInput(input: string): (int, seq<(int, int)>)
    requires |input| > 0
    ensures var n, edges := ParseInput(input); n >= 2 && |edges| == n - 1 ==> ValidInput(n, edges)
{
    // Simplified parsing: assumes input is space-separated numbers
    // First number is n, then pairs of numbers for edges.
    // Example: "3 1 2 2 3" -> n=3, edges=[(1,2), (2,3)]

    var parts := input.Split(' ');
    var n := StringToInt(parts[0]);
    var edges: seq<(int, int)> := [];
    var i := 1;
    while i < |parts| - 1
        invariant 1 <= i <= |parts| - 1
        invariant |edges| == (i - 1) / 2
        invariant forall k :: 0 <= k < |edges| ==> 1 <= edges[k].0 <= n && 1 <= edges[k].1 <= n
    {
        var u := StringToInt(parts[i]);
        var v := StringToInt(parts[i+1]);
        edges := edges + [(u, v)];
        i := i + 2;
    }
    return (n, edges);
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures |output| > 0
// </vc-spec>
// <vc-code>
{
    var (n, edges) := ParseInput(input);

    if !ValidInput(n, edges) then
        return "Invalid Input";

    // A tree with N nodes and N-1 edges is a path graph if it's not a star graph
    // and connecting all nodes to a central node (star graph) ensures all nodes are distance 1 or 2 from each other (from the center node, or from a neighbor of the center node)
    // If the existing graph is already a star graph with center 1, then all vertices are within distance 1 from 1.
    // If the existing graph is distance 2 from 1, it implies no edges need to be added.

    if AllVerticesWithinDistance2(n, edges) then
        return "0"; // Already satisfies the condition
    else
    {
        // Try to make it a star graph with node 1 as center
        // This requires adding edges between node 1 and any node not directly connected to it.
        var adj := BuildAdjacencyList(n, edges);
        var edgesToAdd := 0;
        for v := 2 to n
            invariant 2 <= v <= n + 1
            invariant edgesToAdd >= 0
        {
            if BFS(adj, n, 1, v) > 2 then // If distance is > 2, we need to add an edge.
                // We assume we want to achieve a distance of 1 or 2 by making it a star graph centered at 1.
                // If BFS distance is 1 or 2, no edge is needed for this pair.
                // If BFS distance is > 2, adding an edge (1,v) would reduce the distance to 1.
                edgesToAdd := edgesToAdd + 1;
        }
        return IntToString(edgesToAdd);
    }
}
// </vc-code>

