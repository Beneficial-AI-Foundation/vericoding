// <vc-preamble>
predicate ValidInput(n: int, queries: seq<(int, int)>)
{
    n > 0 && 
    forall i :: 0 <= i < |queries| ==> 1 <= queries[i].0 <= n && 1 <= queries[i].1 <= n
}

function ChessboardValue(n: int, x: int, y: int): int
    requires n > 0
    requires 0 <= x < n && 0 <= y < n
{
    if (x + y) % 2 == 0 then
        1 + (x / 2) * n + (x % 2) * ((n + 1) / 2) + y / 2
    else
        (n * n + 1) / 2 + 1 + (x / 2) * n + (x % 2) * (n / 2) + y / 2
}

predicate ValidResult(n: int, queries: seq<(int, int)>, results: seq<int>)
    requires ValidInput(n, queries)
{
    |results| == |queries| &&
    forall i :: 0 <= i < |queries| ==> 
        var x, y := queries[i].0 - 1, queries[i].1 - 1;
        0 <= x < n && 0 <= y < n &&
        results[i] == ChessboardValue(n, x, y)
}
// </vc-preamble>

// <vc-helpers>
function ComputeChessboardValue(n: int, x: int, y: int): int
    requires n > 0
    requires 0 <= x < n && 0 <= y < n
{
    ChessboardValue(n, x, y)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, queries: seq<(int, int)>) returns (results: seq<int>)
    requires ValidInput(n, queries)
    ensures ValidResult(n, queries, results)
// </vc-spec>
// <vc-code>
{
  var results_array: array<int> := new int[|queries|];
  var i: int := 0;
  while i < |queries|
    invariant 0 <= i <= |queries|
    invariant forall k :: 0 <= k < i ==> results_array[k] == ChessboardValue(n, queries[k].0 - 1, queries[k].1 - 1)
  {
    var x_coord := queries[i].0 - 1;
    var y_coord := queries[i].1 - 1;
    results_array[i] := ComputeChessboardValue(n, x_coord, y_coord);
    i := i + 1;
  }
  results := results_array[..];
}
// </vc-code>
