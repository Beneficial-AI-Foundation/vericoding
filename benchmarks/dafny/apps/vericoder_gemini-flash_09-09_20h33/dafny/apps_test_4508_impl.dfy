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
            invariant forall k' :: 0 <= k' < |numStr| ==> '0' <= numStr[k'] <= '9'
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
    requires |s| > 0 && (forall c :: c in s ==> '0' <= c <= '9')
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
    forall v :: 1 <= v <= n ==> BFS_distance(adj, n, 1, v) != -1
}

function BFS_distance(adj: seq<seq<int>>, n: int, start: int, target: int): int
    requires n >= 1 && |adj| == n + 1 && 1 <= start <= n && 1 <= target <= n
{
    if start == target then 0 else
    var q: seq<int> := [];
    var dist := new seq<int>(n + 1, _ => -1);
    
    q := q + [start];
    dist := dist[start := 0];
    
    var head := 0;
    while head < |q|
        invariant 0 <= head <= |q|
        invariant forall k :: 0 <= k < |q| ==> 1 <= q[k] <= n
        invariant forall k :: 0 <= k < |dist| ==> dist[k] == -1 || (0 <= dist[k] <= n)
        invariant dist[start] == 0
    {
        var u := q[head];
        head := head + 1;
        
        if u == target then return dist[u];
        
        var neighbors := adj[u];
        for v' in neighbors
        {
            var v := v'; 
            if 1 <= v <= n && dist[v] == -1
            {
                if dist[u] + 1 <= n {
                    dist := dist[v := dist[u] + 1];
                    q := q + [v];
                }
            }
        }
    }
    return -1;
}

function IsTree(n: int, edges: seq<(int, int)>): bool
    requires n >= 1
{
    IsConnected(n, edges)
}

predicate AllVerticesWithinDistance2_fixed(n: int, edges: seq<(int, int)>)
    requires n >= 2
{
    forall v :: 2 <= v <= n ==> BFS_distance(BuildAdjacencyList(n, edges), n, 1, v) <= 2 && BFS_distance(BuildAdjacencyList(n, edges), n, 1, v) != -1
}

function ConvertToEdges(numbers: seq<int>, start_index: int): seq<(int, int)>
    requires start_index >= 0
    requires start_index + 1 <= |numbers|
    requires (start_index % 2) == 1
    requires forall i :: start_index <= i < |numbers| ==> numbers[i] >= 1
    ensures |ConvertToEdges(numbers, start_index)| == (|numbers| - start_index) / 2
    decreases |numbers| - start_index
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

    if !(forall e :: e in originalEdges ==> 1 <= e.0 <= n && 1 <= e.1 <= n && e.0 != e.1) then
        return "Invalid edge format (vertices must be within [1, N] and not equal)";
    
    if !(IsTree(n, originalEdges)) then
        return "Input graph is not a tree.";

    if AllVerticesWithinDistance2_fixed(n, originalEdges) then
        return "0";

    var adj := BuildAdjacencyList(n, originalEdges);
    var addedEdgesCount := 0;
    
    var nodesNeedingConnection: seq<int> := [];
    for v := 2 to n
        invariant 2 <= v <= n+1
        invariant forall k :: 0 <= k < |nodesNeedingConnection| ==> 2 <= nodesNeedingConnection[k] <= n
        invariant forall k :: 0 <= k < |nodesNeedingConnection| ==> BFS_distance(adj, n, 1, nodesNeedingConnection[k]) > 2
        invariant addedEdgesCount == |nodesNeedingConnection|
    {
        if BFS_distance(adj, n, 1, v) > 2
        {
            nodesNeedingConnection := nodesNeedingConnection + [v];
            addedEdgesCount := addedEdgesCount + 1;
        }
    }
    
    return addedEdgesCount as string;
}
// </vc-code>

