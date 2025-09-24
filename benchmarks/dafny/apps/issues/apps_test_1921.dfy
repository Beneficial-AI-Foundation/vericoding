// <vc-preamble>
predicate ValidInput(n: int, m: int, sx: int, sy: int, fx: int, fy: int, instantLocations: seq<(int, int)>)
{
    n >= 1 && m >= 0 && |instantLocations| == m &&
    1 <= sx <= n && 1 <= sy <= n &&
    1 <= fx <= n && 1 <= fy <= n &&
    (forall i :: 0 <= i < m ==> 1 <= instantLocations[i].0 <= n && 1 <= instantLocations[i].1 <= n)
}

function ManhattanDistance(x1: int, y1: int, x2: int, y2: int): int
{
    abs(x1 - x2) + abs(y1 - y2)
}

function DirectDistance(sx: int, sy: int, fx: int, fy: int): int
{
    ManhattanDistance(sx, sy, fx, fy)
}

predicate CanTeleport(sx: int, sy: int, tx: int, ty: int)
{
    sx == tx || sy == ty
}

function abs(x: int): int
{
    if x >= 0 then x else -x
}
// </vc-preamble>

// <vc-helpers>
method dijkstra(graph: array<seq<(int, int)>>, numNodes: int, start: int) returns (distances: seq<int>)
    requires graph.Length == numNodes
    requires numNodes >= 1
    requires 0 <= start < numNodes
    requires forall i :: 0 <= i < numNodes ==> forall j :: 0 <= j < |graph[i]| ==> 0 <= graph[i][j].0 < numNodes && graph[i][j].1 >= 0
    ensures |distances| == numNodes
    ensures forall i :: 0 <= i < numNodes ==> distances[i] >= 0
    ensures distances[start] == 0
{
    distances := seq(numNodes, _ => 1000000000);
    distances := distances[start := 0];

    var visited := seq(numNodes, _ => false);
    var processed := 0;

    while processed < numNodes
        decreases numNodes - processed
        invariant |distances| == numNodes
        invariant |visited| == numNodes
        invariant forall i :: 0 <= i < numNodes ==> distances[i] >= 0
        invariant distances[start] == 0
        invariant 0 <= processed <= numNodes
    {
        var minNode := -1;
        var minDist := 1000000001;
        var i := 0;
        while i < numNodes
            invariant 0 <= i <= numNodes
            invariant minNode == -1 || (0 <= minNode < numNodes && !visited[minNode])
            invariant minNode == -1 ==> minDist == 1000000001
            invariant minNode != -1 ==> minDist == distances[minNode]
            invariant forall k :: 0 <= k < i ==> visited[k] || distances[k] >= minDist
        {
            if !visited[i] && distances[i] < minDist {
                minNode := i;
                minDist := distances[i];
            }
            i := i + 1;
        }

        if minNode == -1 {
            break;
        }

        visited := visited[minNode := true];
        processed := processed + 1;

        var neighbors := graph[minNode];
        i := 0;
        while i < |neighbors|
            invariant |distances| == numNodes
            invariant |visited| == numNodes
            invariant forall k :: 0 <= k < numNodes ==> distances[k] >= 0
            invariant distances[start] == 0
        {
            var neighbor := neighbors[i].0;
            var weight := neighbors[i].1;
            var newDist := distances[minNode] + weight;

            if newDist < distances[neighbor] {
                distances := distances[neighbor := newDist];
            }
            i := i + 1;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, sx: int, sy: int, fx: int, fy: int, instantLocations: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, m, sx, sy, fx, fy, instantLocations)
    ensures result >= 0
    ensures result <= DirectDistance(sx, sy, fx, fy)
    ensures m == 0 ==> result == DirectDistance(sx, sy, fx, fy)
// </vc-spec>
// <vc-code>
{
    var directDistance := DirectDistance(sx, sy, fx, fy);

    if m == 0 {
        return directDistance;
    }

    var numNodes := m + 2;
    var startNode := m;
    var endNode := m + 1;

    var graph := new seq<(int, int)>[numNodes];
    var i := 0;
    while i < numNodes
        invariant 0 <= i <= numNodes
        invariant forall k :: 0 <= k < i ==> graph[k] == []
    {
        graph[i] := [];
        i := i + 1;
    }

    i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant forall k :: 0 <= k < numNodes ==> forall j :: 0 <= j < |graph[k]| ==> 0 <= graph[k][j].0 < numNodes && graph[k][j].1 >= 0
    {
        var j := i + 1;
        while j < m
            invariant i < j <= m
            invariant forall k :: 0 <= k < numNodes ==> forall l :: 0 <= l < |graph[k]| ==> 0 <= graph[k][l].0 < numNodes && graph[k][l].1 >= 0
        {
            var loc1 := instantLocations[i];
            var loc2 := instantLocations[j];
            if loc1.0 == loc2.0 || loc1.1 == loc2.1 {
                var cost := ManhattanDistance(loc1.0, loc1.1, loc2.0, loc2.1);
                graph[i] := graph[i] + [(j, cost)];
                graph[j] := graph[j] + [(i, cost)];
            }
            j := j + 1;
        }
        i := i + 1;
    }

    i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant forall k :: 0 <= k < numNodes ==> forall j :: 0 <= j < |graph[k]| ==> 0 <= graph[k][j].0 < numNodes && graph[k][j].1 >= 0
    {
        var loc := instantLocations[i];
        if CanTeleport(sx, sy, loc.0, loc.1) {
            graph[startNode] := graph[startNode] + [(i, 0)];
        } else {
            var cost := ManhattanDistance(sx, sy, loc.0, loc.1);
            graph[startNode] := graph[startNode] + [(i, cost)];
        }
        i := i + 1;
    }

    i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant forall k :: 0 <= k < numNodes ==> forall j :: 0 <= j < |graph[k]| ==> 0 <= graph[k][j].0 < numNodes && graph[k][j].1 >= 0
    {
        var loc := instantLocations[i];
        var cost := ManhattanDistance(loc.0, loc.1, fx, fy);
        graph[i] := graph[i] + [(endNode, cost)];
        i := i + 1;
    }

    graph[startNode] := graph[startNode] + [(endNode, directDistance)];

    var distances := dijkstra(graph, numNodes, startNode);

    result := if distances[endNode] < directDistance then distances[endNode] else directDistance;
}
// </vc-code>
