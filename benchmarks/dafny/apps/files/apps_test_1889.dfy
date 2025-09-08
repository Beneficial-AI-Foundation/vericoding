Given an n×m grid where each cell contains either 0 or 1, process q queries.
Each query flips the value at position (i,j) from 0 to 1 or 1 to 0.
After each query, calculate the score: the maximum length of consecutive 1s across all rows in the grid.

predicate ValidGrid(grid: seq<seq<int>>, n: int, m: int)
{
    |grid| == n && n > 0 && m > 0 &&
    (forall i :: 0 <= i < n ==> |grid[i]| == m) &&
    (forall i, j :: 0 <= i < n && 0 <= j < m ==> grid[i][j] == 0 || grid[i][j] == 1)
}

predicate ValidQueries(queries: seq<(int, int)>, q: int, n: int, m: int)
{
    |queries| == q && q >= 0 &&
    (forall k :: 0 <= k < q ==> 1 <= queries[k].0 <= n && 1 <= queries[k].1 <= m)
}

function ConsHelper(l: seq<int>, index: int, current: int, maxSoFar: int): int
    requires 0 <= index
    decreases |l| - index
{
    if index >= |l| then maxSoFar
    else if l[index] == 1 then
        var newCurrent := current + 1;
        var newMax := if newCurrent > maxSoFar then newCurrent else maxSoFar;
        ConsHelper(l, index + 1, newCurrent, newMax)
    else
        ConsHelper(l, index + 1, 0, maxSoFar)
}

function cons(l: seq<int>): int
{
    ConsHelper(l, 0, 0, 0)
}

function MaxInSeq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else 
        var rest := MaxInSeq(s[1..]);
        if s[0] > rest then s[0] else rest
}

function ComputeScore(grid: seq<seq<int>>): int
    requires |grid| > 0
    requires forall i :: 0 <= i < |grid| ==> |grid[i]| > 0
{
    var rowScores := seq(|grid|, i requires 0 <= i < |grid| => cons(grid[i]));
    MaxInSeq(rowScores)
}

function ApplyQuery(grid: seq<seq<int>>, query: (int, int)): seq<seq<int>>
    requires |grid| > 0
    requires forall i :: 0 <= i < |grid| ==> |grid[i]| > 0
    requires 0 <= query.0 < |grid| && 0 <= query.1 < |grid[0]|
    requires forall i :: 0 <= i < |grid| ==> |grid[i]| == |grid[0]|
    ensures |ApplyQuery(grid, query)| == |grid|
    ensures forall i :: 0 <= i < |grid| ==> |ApplyQuery(grid, query)[i]| == |grid[i]|
    ensures forall i :: 0 <= i < |grid| ==> |ApplyQuery(grid, query)[i]| == |grid[0]|
{
    var row := grid[query.0];
    var newRow := row[query.1 := if row[query.1] == 0 then 1 else 0];
    grid[query.0 := newRow]
}

method solve(n: int, m: int, q: int, grid: seq<seq<int>>, queries: seq<(int, int)>) returns (results: seq<int>)
    requires ValidGrid(grid, n, m)
    requires ValidQueries(queries, q, n, m)
    ensures |results| == q
{
    var currentGrid := grid;
    var curr := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant curr.Length == n
    {
        curr[i] := cons(currentGrid[i]);
        i := i + 1;
    }

    results := [];
    var queryIndex := 0;
    while queryIndex < q
        invariant 0 <= queryIndex <= q
        invariant |results| == queryIndex
        invariant |currentGrid| == n
        invariant forall i :: 0 <= i < n ==> |currentGrid[i]| == m
    {
        var queryI := queries[queryIndex].0 - 1;
        var queryJ := queries[queryIndex].1 - 1;

        var newRow := currentGrid[queryI];
        newRow := newRow[queryJ := if newRow[queryJ] == 0 then 1 else 0];
        currentGrid := currentGrid[queryI := newRow];

        curr[queryI] := cons(newRow);

        var maxVal := 0;
        var j := 0;
        while j < n
            invariant 0 <= j <= n
            invariant maxVal >= 0
        {
            if curr[j] > maxVal {
                maxVal := curr[j];
            }
            j := j + 1;
        }

        results := results + [maxVal];
        queryIndex := queryIndex + 1;
    }
}
