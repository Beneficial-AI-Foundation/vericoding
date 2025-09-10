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
// No changes needed; existing helpers suffice.
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, q: int, grid: seq<seq<int>>, queries: seq<(int, int)>) returns (results: seq<int>)
    requires ValidGrid(grid, n, m)
    requires ValidQueries(queries, q, n, m)
    ensures |results| == q
// </vc-spec>
// <vc-code>
{
    var localGrid := grid;
    var rowScores := seq(n, i requires 0 <= i < n => cons(grid[i]));
    var currentMax := MaxInSeq(rowScores);
    results := [];
    var i := 0;
    while i < q
        invariant 0 <= i <= q
        invariant |results| == i
        invariant |localGrid| == n
        invariant forall i :: 0 <= i < n ==> |localGrid[i]| == m
        invariant |rowScores| == n
        invariant forall i,j :: 0 <= i < n && 0 <= j < m ==> localGrid[i][j] == 0 || localGrid[i][j] == 1
    {
        var (x, y) := queries[i];
        var ri := x - 1;
        var cj := y - 1;
        var newVal := 1 - localGrid[ri][cj];
        var updatedRow := localGrid[ri][cj := newVal];
        var updatedGrid := localGrid[ri := updatedRow];
        localGrid := updatedGrid;
        var newRowScore := cons(updatedGrid[ri]);
        rowScores := rowScores[ri := newRowScore];
        currentMax := MaxInSeq(rowScores);
        results := results + [currentMax];
        i := i + 1;
    }}
// </vc-code>

