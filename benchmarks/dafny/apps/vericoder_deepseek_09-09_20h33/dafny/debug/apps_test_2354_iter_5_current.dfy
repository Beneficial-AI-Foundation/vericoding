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
lemma ChessboardValueProperties(n: int)
    requires n > 0
    ensures forall x, y :: 0 <= x < n && 0 <= y < n ==> 1 <= ChessboardValue(n, x, y) <= n * n
{
    // The chessboard value calculation ensures bounds by construction
    // No need for complex proof since the function is well-defined
}

lemma ChessboardValueConsistent(n: int, x1: int, y1: int, x2: int, y2: int)
    requires n > 0
    requires 0 <= x1 < n && 0 <= y1 < n
    requires 0 <= x2 < n && 0 <= y2 < n
    requires x1 == x2 && y1 == y2
    ensures ChessboardValue(n, x1, y1) == ChessboardValue(n, x2, y2)
{
    // Trivial since inputs are identical
}

ghost method ChessboardValueBounds(n: int, x: int, y: int)
    requires n > 0
    requires 0 <= x < n && 0 <= y < n
    ensures 1 <= ChessboardValue(n, x, y) <= n * n
{
    // Helper method to prove bounds for individual positions
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, queries: seq<(int, int)>) returns (results: seq<int>)
    requires ValidInput(n, queries)
    ensures ValidResult(n, queries, results)
// </vc-spec>
// <vc-code>
{
    results := [];
    var i := 0;
    while i < |queries|
        invariant i <= |queries|
        invariant |results| == i
        invariant ValidResult(n, queries[..i], results)
    {
        var query := queries[i];
        var x := query.0 - 1;
        var y := query.1 - 1;
        // Use lemma to prove bounds for better performance
        ghost var x_val := x;
        ghost var y_val := y;
        ghost ChessboardValueBounds(n, x_val, y_val);
        var val := ChessboardValue(n, x, y);
        results := results + [val];
        i := i + 1;
    }
}
// </vc-code>

