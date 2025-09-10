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
        var value := ChessboardValue(n, x, y);
        // Base case: minimum value is always 1 (when x=0, y=0 and even)
        if (x + y) % 2 == 0 {
            // Even part: values from 1 to (n*n + 1)/2
            assert 1 + (x / 2) * n + (x % 2) * ((n + 1) / 2) + y / 2 >= 1;
            assert 1 + (x / 2) * n + (x % 2) * ((n + 1) / 2) + y / 2 <= 1 + ((n-1)/2)*n + ((n + 1)/2) + (n-1)/2;
        } else {
            // Odd part: values from (n*n + 1)/2 + 1 to n*n
            assert (n * n + 1) / 2 + 1 + (x / 2) * n + (x % 2) * (n / 2) + y / 2 >= (n * n + 1) / 2 + 1;
            assert (n * n + 1) / 2 + 1 + (x / 2) * n + (x % 2) * (n / 2) + y / 2 <= n * n;
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
        assert 0 <= x < n && 0 <= y < n; // This should hold by ValidInput
        var val := ChessboardValue(n, x, y);
        ChessboardValueProperties(n); // Help the verifier with the property
        results := results + [val];
        i := i + 1;
    }
}
// </vc-code>

