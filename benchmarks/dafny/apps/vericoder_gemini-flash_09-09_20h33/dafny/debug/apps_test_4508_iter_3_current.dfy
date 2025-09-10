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
function GetInputIntegers(input: string): seq<int>
    requires |input| > 0
{
    var numbers: seq<int> := []; // Initialize as empty sequence
    var i := 0;
    while i < |input|
        invariant 0 <= i <= |input|
        invariant forall k :: 0 <= k < |numbers| ==> numbers[k] >= 0
    {
        var numStr := "";
        while i < |input| && '0' <= input[i] <= '9'
            invariant i <= |input|
            invariant forall k :: 0 <= k < |numbers| ==> numbers[k] >= 0
            invariant forall k :: 0 <= k < |numStr| ==> '0' <= numStr[k] <= '9'
        {
            numStr := numStr + input[i];
            i := i + 1;
        }
        if |numStr| > 0
        {
            numbers := numbers + [string_to_int(numStr)];
        }
        if i < |input| && (input[i] == ' ' || input[i] == ',' || input[i] == ';')
        {
            i := i + 1;
        }
    }
    return numbers;
}

function string_to_int(s: string): int
    requires |s| > 0 && (forall c :: '0' <= c <= '9' ==> c in s) // simplified, actual implementation would parse digits
    ensures string_to_int(s) >= 0
{
  var result := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result >= 0
  {
    result := result * 10 + (s[i] - '0');
    i := i + 1;
  }
  return result;
}

predicate IsConnected(n: int, edges: seq<(int, int)>)
    requires n >= 1
{
    var adj := BuildAdjacencyList(n, edges);
    forall v :: 1 <= v <= n ==> BFS_distance(adj, n, 1, v) < n // A node is reachable if distance < n
}

// Method to perform BFS and return the distance, or -1 if not reachable
function BFS_distance(adj: seq<seq<int>>, n: int, start: int, target: int): int
    requires n >= 1 && |adj| == n + 1 && 1 <= start <= n && 1 <= target <= n
{
    if start == target then 0 else
    var q: seq<int> := []; // Initialize as empty sequence
    var dist := new seq<int>(n + 1, _ => -1); // -1 indicates unvisited
    
    q := q + [start];
    dist := dist[start := 0];
    
    var head := 0;
    while head < |q|
        invariant 0 <= head <= |q|
        invariant forall k :: 0 <= k < |q| ==> 1 <= q[k] <= n
        invariant forall k :: 0 <= k < |dist| ==> dist[k] == -1 || (0 <= dist[k] <= n) // Distance bounded by n or n-1 if connected for real graphs. Changed from < n to <= n since dist can eventually reach n.
        invariant dist[start] == 0
    {
        var u := q[head];
        head := head + 1;
        
        if u == target then return dist[u];
        
        var neighbors := adj[u];
        for v' in neighbors // Use v' to avoid clash with loop variable
            // Invariants for `for` loop are tricky and often depend on the specific loop structure.
            // For now, let's focus on the `if` condition within the loop.
        {
            var v := v'; // Use v for cleaner access in the if condition
            if 1 <= v <= n && dist[v] == -1 // If v is valid and unvisited
            {
                // Ensure dist[u] + 1 does not exceed n
                if dist[u] + 1 <= n {
                    dist := dist[v := dist[u] + 1];
                    q := q + [v];
                }
            }
        }
    }
    return -1; // Target not reachable
}

function IsTree(n: int, edges: seq<(int, int)>): bool
    requires n >= 1
{
    // A graph with N vertices and N-1 edges is a tree if and only if it is connected.
    // Assuming no self-loops or multi-edges for simplicity in this check
    // The ValidInput predicate already ensures |edges| == n - 1
    // We just need to check for connectivity
    IsConnected(n, edges)
}

predicate AllVerticesWithinDistance2_fixed(n: int, edges: seq<(int, int)>)
    requires n >= 2
{
    forall v :: 2 <= v <= n ==> BFS_distance(BuildAdjacencyList(n, edges), n, 1, v) <= 2
}

// Function to convert seq<int> to seq<(int, int)> for edges
function ConvertToEdges(numbers: seq<int>, start_index: int): seq<(int, int)>
    requires start_index >= 0 && (start_index % 2) == 0
    requires (start_index + 1) <= |numbers|
    requires forall i :: start_index <= i < |numbers| ==> numbers[i] >= 1
    ensures |ConvertToEdges(numbers, start_index)| == (|numbers| - start_index) / 2
{
    if start_index + 1 >= |numbers| then
        []
    else
        [(numbers[start_index], numbers[start_index + 1])] + ConvertToEdges(numbers, start_index + 2)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures |output| > 0
// </vc-spec>
// <vc-code>
{
    var numbers := GetInputIntegers(input);
    if |numbers| < 2 then
        return "Invalid input format";
    
    var n := numbers[0];
    if n < 2 then
        return "Invalid number of vertices (N must be >= 2)";

    var originalEdges := ConvertToEdges(numbers, 1);
    
    if |originalEdges| != n - 1 then
        return "Invalid number of edges (N-1 edges required for tree)";

    // Validate edge values: 1 <= u, v <= n and u != v
    if !(forall e :: e in originalEdges ==> 1 <= e.0 <= n && 1 <= e.1 <= n && e.0 != e.1) then
        return "Invalid edge format (vertices must be within [1, N] and not equal)";
    
    // Check if the initial graph is a tree (connected and N-1 edges)
    // The `ValidInput` predicate covers N-1 edges and valid vertex ranges;
    // We explicitly check connectivity here using BFS_distance for all pairs from node 1.
    if !(IsTree(n, originalEdges)) then
        return "Input graph is not a tree.";

    // Check if all vertices are already within distance 2 from vertex 1
    if AllVerticesWithinDistance2_fixed(n, originalEdges) then
        return "0"; // All vertices within distance 2, no edges needed.

    var adj := BuildAdjacencyList(n, originalEdges);
    var addedEdgesCount := 0;
    
    var nodesNeedingConnection: seq<int> := [];
    for v := 2 to n
        invariant 2 <= v <= n+1
        invariant forall k :: 0 <= k < |nodesNeedingConnection| ==> 2 <= nodesNeedingConnection[k] <= n
    {
        if BFS_distance(adj, n, 1, v) > 2
        {
            nodesNeedingConnection := nodesNeedingConnection + [v];
        }
    }
    
    addedEdgesCount := |nodesNeedingConnection|;

    return addedEdgesCount as string;
}
// </vc-code>

