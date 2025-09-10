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

// <vc-helpers>
function GetChessboardValue(n: int, x: int, y: int): int
    requires n > 0
    requires 0 <= x < n && 0 <= y < n
{
    if (x + y) % 2 == 0 then
        1 + (x / 2) * n + (x % 2) * ((n + 1) / 2) + y / 2
    else
        (n * n + 1) / 2 + 1 + (x / 2) * n + (x % 2) * (n / 2) + y / 2
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, queries: seq<(int, int)>) returns (results: seq<int>)
    requires ValidInput(n, queries)
    ensures ValidResult(n, queries, results)
// </vc-spec>
// <vc-code>
{
    var res_array: array<int> := new int[|queries|];
    for i := 0 to |queries| - 1
        invariant 0 <= i <= |queries|
        invariant res_array.Length == |queries|
        invariant forall k :: 0 <= k < i ==> 
            var x_k, y_k := queries[k].0 - 1, queries[k].1 - 1;
            res_array[k] == ChessboardValue(n, x_k, y_k)
    {
        var x_coord := queries[i].0 - 1;
        var y_coord := queries[i].1 - 1;
        res_array[i] := ChessboardValue(n, x_coord, y_coord);
    }
    return res_array[..];
}
// </vc-code>

