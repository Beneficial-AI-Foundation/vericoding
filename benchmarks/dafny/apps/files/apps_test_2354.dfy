Fill an n×n chessboard with numbers 1 to n² using a specific pattern:
Place first ⌈n²/2⌉ numbers in cells where (row + column) is even, filling left-to-right, top-to-bottom
Place remaining numbers in cells where (row + column) is odd, filling left-to-right, top-to-bottom
For given queries (xi, yi), return the number at each position

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

method solve(n: int, queries: seq<(int, int)>) returns (results: seq<int>)
    requires ValidInput(n, queries)
    ensures ValidResult(n, queries, results)
{
    results := [];
    for i := 0 to |queries|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> 
            var x, y := queries[j].0 - 1, queries[j].1 - 1;
            0 <= x < n && 0 <= y < n &&
            results[j] == ChessboardValue(n, x, y)
    {
        var x, y := queries[i].0 - 1, queries[i].1 - 1;

        var res: int;
        if (x + y) % 2 == 0 {
            res := 1;
            res := res + (x / 2) * n;
            res := res + (x % 2) * ((n + 1) / 2);
            res := res + y / 2;
        } else {
            res := (n * n + 1) / 2 + 1;
            res := res + (x / 2) * n;
            res := res + (x % 2) * (n / 2);
            res := res + y / 2;
        }

        results := results + [res];
    }
}
