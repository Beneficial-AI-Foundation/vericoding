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
    ensures n >= 2
{
    // Parse the first line to get n
    var lines := SplitLines(input);
    if |lines| == 0 {
        n := 2;
        edges := [];
        return;
    }
    
    n := ParseInt(lines[0]);
    if n < 2 {
        n := 2;
    }
    
    edges := [];
    var i := 1;
    while i < |lines| && |edges| < n - 1
    {
        var parts := SplitSpace(lines[i]);
        if |parts| >= 2 {
            var u := ParseInt(parts[0]);
            var v := ParseInt(parts[1]);
            edges := edges + [(u, v)];
        }
        i := i + 1;
    }
}

method SplitLines(s: string) returns (lines: seq<string>)
    ensures |lines| >= 0
{
    lines := [];
    var current := "";
    var i := 0;
    while i < |s|
    {
        if s[i] == '\n' {
            lines := lines + [current];
            current := "";
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }
    if |current| > 0 {
        lines := lines + [current];
    }
}

method SplitSpace(s: string) returns (parts: seq<string>)
    ensures |parts| >= 0
{
    parts := [];
    var current := "";
    var i := 0;
    while i < |s|
    {
        if s[i] == ' ' {
            if |current| > 0 {
                parts := parts + [current];
                current := "";
            }
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }
    if |current| > 0 {
        parts := parts + [current];
    }
}

method ParseInt(s: string) returns (n: int)
    ensures n >= 0
{
    n := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant n >= 0
    {
        if '0' <= s[i] <= '9' {
            n := n * 10 + (s[i] as int - '0' as int);
        }
        i := i + 1;
    }
}

method IntToString(n: int) returns (s: string)
    requires n >= 0
    ensures |s| > 0
{
    if n == 0 {
        s := "0";
    } else {
        s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant temp == 0 ==> |s| > 0
        {
            var digit := temp % 10;
            var ch := (('0' as int + digit) as char);
            s := [ch] + s;
            temp := temp / 10;
        }
        if |s| == 0 {  // Safety check to ensure postcondition
            s := "0";
        }
    }
}

method ComputeMinEdgesToAdd(n: int, edges: seq<(int, int)>) returns (count: int)
    requires n >= 2
    ensures count >= 0
{
    // Build adjacency list
    var adj := new seq<int>[n + 1];
    var i := 0;
    while i <= n
    {
        adj[i] := [];
        i := i + 1;
    }
    
    // Add edges to adjacency list
    i := 0;
    while i < |edges|
    {
        var u := edges[i].0;
        var v := edges[i].1;
        if 1 <= u <= n && 1 <= v <= n {
            adj[u] := adj[u] + [v];
            adj[v] := adj[v] + [u];
        }
        i := i + 1;
    }
    
    // Count vertices not within distance 2 from vertex 1
    count := 0;
    var v := 2;
    while v <= n
    {
        var dist := ComputeDistance(adj, n, 1, v);
        if dist > 2 {
            count := count + 1;
        }
        v := v + 1;
    }
}

method ComputeDistance(adj: array<seq<int>>, n: int, start: int, end: int) returns (dist: int)
    requires adj.Length == n + 1
    requires 1 <= start <= n && 1 <= end <= n
    ensures dist >= 0
{
    if start == end {
        dist := 0;
        return;
    }
    
    // Check if directly connected
    if end in adj[start] {
        dist := 1;
        return;
    }
    
    // Check if connected through one intermediate vertex
    var i := 0;
    while i < |adj[start]|
    {
        var neighbor := adj[start][i];
        if 1 <= neighbor <= n && end in adj[neighbor] {
            dist := 2;
            return;
        }
        i := i + 1;
    }
    
    dist := 3; // More than 2
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
    var minEdges := ComputeMinEdgesToAdd(n, edges);
    output := IntToString(minEdges);
}
// </vc-code>

