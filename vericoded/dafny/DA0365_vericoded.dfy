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

// <vc-helpers>
lemma ValidGridAfterToggle(grid: seq<seq<int>>, n: int, m: int, i: int, j: int)
    requires ValidGrid(grid, n, m)
    requires 0 <= i < n && 0 <= j < m
    ensures var newGrid := grid[i := grid[i][j := 1 - grid[i][j]]];
            ValidGrid(newGrid, n, m)
{
    var newGrid := grid[i := grid[i][j := 1 - grid[i][j]]];
    assert |newGrid| == n;
    assert forall k :: 0 <= k < n ==> |newGrid[k]| == m;
    assert forall k, l :: 0 <= k < n && 0 <= l < m ==> 
        newGrid[k][l] == 0 || newGrid[k][l] == 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, q: int, grid: seq<seq<int>>, queries: seq<(int, int)>) returns (results: seq<int>)
    requires ValidGrid(grid, n, m)
    requires ValidQueries(queries, q, n, m)
    ensures |results| == q
// </vc-spec>
// <vc-code>
{
    results := [];
    var currentGrid := grid;
    
    for k := 0 to q
        invariant 0 <= k <= q
        invariant |results| == k
        invariant ValidGrid(currentGrid, n, m)
    {
        var (row, col) := queries[k];
        var i := row - 1;  // Convert to 0-indexed
        var j := col - 1;  // Convert to 0-indexed
        
        // Toggle the cell
        var newRow := currentGrid[i][j := 1 - currentGrid[i][j]];
        currentGrid := currentGrid[i := newRow];
        
        ValidGridAfterToggle(grid, n, m, i, j);
        
        // Compute score and append to results
        var score := ComputeScore(currentGrid);
        results := results + [score];
    }
}
// </vc-code>

