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
    forall x, y | 0 <= x < n && 0 <= y < n
        ensures 1 <= ChessboardValue(n, x, y) <= n * n
    {
        if (x + y) % 2 == 0 {
            // Even case: 1 ≤ value ≤ (n*n+1)/2
            var value := 1 + (x / 2) * n + (x % 2) * ((n + 1) / 2) + y / 2;
            assert value >= 1;  // Minimum when x=0,y=0
            if n % 2 == 0 {
                assert value <= (n*n)/2;  // For even n
            } else {
                assert value <= (n*n+1)/2;  // For odd n
            }
        } else {
            // Odd case: (n*n+1)/2 + 1 ≤ value ≤ n*n
            var value := (n * n + 1) / 2 + 1 + (x / 2) * n + (x % 2) * (n / 2) + y / 2;
            if n % 2 == 0 {
                assert value >= (n*n)/2 + 1;  // For even n
            } else {
                assert value >= (n*n+1)/2 + 1;  // For odd n
            }
            assert value <= n * n;  // Maximum when x=n-1,y=n-1
        }
    }
}

lemma ChessboardValueConsistent(n: int, x1: int, y1: int, x2: int, y2: int)
    requires n > 0
    requires 0 <= x1 < n && 0 <= y1 < n
    requires 0 <= x2 < n && 0 <= y2 < n
    requires x1 == x2 && y1 == y2
    ensures ChessboardValue(n, x1, y1) == ChessboardValue(n, x2, y2)
{
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
        invariant forall j :: 0 <= j < i ==> 
            var x, y := queries[j].0 - 1, queries[j].1 - 1;
            results[j] == ChessboardValue(n, x, y)
    {
        var query := queries[i];
        var x := query.0 - 1;
        var y := query.1 - 1;
        // The ValidInput precondition already ensures 1 ≤ query.0 ≤ n and 1 ≤ query.1 ≤ n
        // So x and y are in 0..n-1
        var val := ChessboardValue(n, x, y);
        results := results + [val];
        i := i + 1;
    }
}
// </vc-code>

