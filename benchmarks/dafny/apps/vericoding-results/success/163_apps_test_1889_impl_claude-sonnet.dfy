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
lemma GridNonEmpty(grid: seq<seq<int>>, n: int, m: int)
    requires ValidGrid(grid, n, m)
    ensures |grid| > 0 && (forall i :: 0 <= i < |grid| ==> |grid[i]| > 0)
{
}

function UpdateGrid(grid: seq<seq<int>>, row: int, col: int): seq<seq<int>>
    requires |grid| > 0
    requires 0 <= row < |grid|
    requires 0 <= col < |grid[row]|
    requires forall i :: 0 <= i < |grid| ==> |grid[i]| == |grid[0]|
    ensures |UpdateGrid(grid, row, col)| == |grid|
    ensures forall i :: 0 <= i < |grid| ==> |UpdateGrid(grid, row, col)[i]| == |grid[i]|
{
    grid[row := grid[row][col := 1 - grid[row][col]]]
}

lemma UpdateGridPreservesSize(grid: seq<seq<int>>, row: int, col: int)
    requires |grid| > 0
    requires 0 <= row < |grid|
    requires 0 <= col < |grid[row]|
    requires forall i :: 0 <= i < |grid| ==> |grid[i]| == |grid[0]|
    ensures var newGrid := UpdateGrid(grid, row, col);
            |newGrid| == |grid| &&
            (forall i :: 0 <= i < |grid| ==> |newGrid[i]| == |grid[i]|)
{
}

lemma UpdateGridPreservesValidGrid(grid: seq<seq<int>>, row: int, col: int, n: int, m: int)
    requires ValidGrid(grid, n, m)
    requires 0 <= row < n
    requires 0 <= col < m
    ensures ValidGrid(UpdateGrid(grid, row, col), n, m)
{
    var newGrid := UpdateGrid(grid, row, col);
    assert |newGrid| == n;
    assert forall i :: 0 <= i < n ==> |newGrid[i]| == m;
    
    forall i, j | 0 <= i < n && 0 <= j < m
        ensures newGrid[i][j] == 0 || newGrid[i][j] == 1
    {
        if i == row && j == col {
            assert newGrid[i][j] == 1 - grid[i][j];
            assert grid[i][j] == 0 || grid[i][j] == 1;
            assert newGrid[i][j] == 0 || newGrid[i][j] == 1;
        } else {
            assert newGrid[i][j] == grid[i][j];
            assert grid[i][j] == 0 || grid[i][j] == 1;
        }
    }
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
    var currentGrid := grid;
    results := [];
    
    var i := 0;
    while i < q
        invariant 0 <= i <= q
        invariant |results| == i
        invariant ValidGrid(currentGrid, n, m)
    {
        GridNonEmpty(currentGrid, n, m);
        var score := ComputeScore(currentGrid);
        results := results + [score];
        
        if i < q {
            var row := queries[i].0 - 1;
            var col := queries[i].1 - 1;
            UpdateGridPreservesSize(currentGrid, row, col);
            UpdateGridPreservesValidGrid(currentGrid, row, col, n, m);
            currentGrid := UpdateGrid(currentGrid, row, col);
        }
        
        i := i + 1;
    }
}
// </vc-code>

