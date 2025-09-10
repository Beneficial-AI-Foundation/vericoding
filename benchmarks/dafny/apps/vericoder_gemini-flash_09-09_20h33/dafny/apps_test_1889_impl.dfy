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
function UpdateGrid(grid: seq<seq<int>>, n: int, m: int, row: int, col: int): seq<seq<int>>
  requires ValidGrid(grid, n, m)
  requires 1 <= row <= n && 1 <= col <= m
  ensures ValidGrid(UpdateGrid(grid, n, m, row, col), n, m)
{
  var r_idx := row - 1;
  var c_idx := col - 1;
  var row_to_update := grid[r_idx];
  var updated_cell_value := 1 - row_to_update[c_idx];
  var updated_row := row_to_update[c_idx := updated_cell_value];
  return grid[r_idx := updated_row];
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
  var results_seq := new int[q];

  for k := 0 to q - 1
    invariant 0 <= k <= q
    invariant ValidGrid(currentGrid, n, m)
    invariant forall i :: 0 <= i < k ==> 0 <= results_seq[i] <= m
    invariant |results_seq| == q
  {
    var r := queries[k].0;
    var c := queries[k].1;

    currentGrid := UpdateGrid(currentGrid, n, m, r, c);
    results_seq[k] := ComputeScore(currentGrid);
  }

  return results_seq[..];
}
// </vc-code>

