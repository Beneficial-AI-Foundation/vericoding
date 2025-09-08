Given q queries with battery charge k, n turns, and two actions with costs a and b (where b < a),
find the maximum number of Action A turns possible while completing exactly n turns and keeping
charge > 0 at the end, or return -1 if impossible.

predicate ValidQuery(k: int, n: int, a: int, b: int)
{
    k > 0 && n > 0 && a > 0 && b > 0 && b < a
}

function MaxActionATurns(k: int, n: int, a: int, b: int): int
    requires ValidQuery(k, n, a, b)
{
    if n * b > k then 
        -1
    else 
        var maxPossible := (k - n * b - 1) / (a - b);
        if n <= maxPossible then n else maxPossible
}

predicate ValidResult(result: int, k: int, n: int, a: int, b: int)
    requires ValidQuery(k, n, a, b)
{
    result == -1 || (0 <= result <= n)
}

method solve(queries: seq<(int, int, int, int)>) returns (results: seq<int>)
    requires |queries| > 0
    requires forall i :: 0 <= i < |queries| ==> 
        var (k, n, a, b) := queries[i];
        ValidQuery(k, n, a, b)
    ensures |results| == |queries|
    ensures forall i :: 0 <= i < |queries| ==> 
        var (k, n, a, b) := queries[i];
        results[i] == MaxActionATurns(k, n, a, b)
    ensures forall i :: 0 <= i < |results| ==> 
        var (k, n, a, b) := queries[i];
        ValidResult(results[i], k, n, a, b)
{
    var output: seq<int> := [];

    for i := 0 to |queries| 
        invariant 0 <= i <= |queries|
        invariant |output| == i
        invariant forall j :: 0 <= j < i ==> 
            var (k, n, a, b) := queries[j];
            output[j] == MaxActionATurns(k, n, a, b)
        invariant forall j :: 0 <= j < i ==> 
            var (k, n, a, b) := queries[j];
            ValidResult(output[j], k, n, a, b)
    {
        var query := queries[i];
        var k := query.0;
        var n := query.1;
        var a := query.2;
        var b := query.3;

        if n * b > k {
            output := output + [-1];
        } else {
            var maxActionA := if n < (k - n * b - 1) / (a - b) then n else (k - n * b - 1) / (a - b);
            output := output + [maxActionA];
        }
    }

    results := output;
}
