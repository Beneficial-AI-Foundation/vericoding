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

// <vc-helpers>
lemma MaxActionATurnsLemma(k: int, n: int, a: int, b: int) 
    requires ValidQuery(k, n, a, b)
    ensures MaxActionATurns(k, n, a, b) == (if n * b >= k then -1 else 
        var diff := a - b;
        var available := k - n * b - 1;
        var maxA := available / diff;
        if maxA >= n then n else maxA)
{
}

lemma MaxActionATurnsRange(k: int, n: int, a: int, b: int)
    requires ValidQuery(k, n, a, b)
    ensures MaxActionATurns(k, n, a, b) >= -1
    ensures MaxActionATurns(k, n, a, b) <= n
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
    results := [];
    var i := 0;
    while i < |queries|
        invariant i <= |queries|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> 
            var (k, n, a, b) := queries[j];
            results[j] == MaxActionATurns(k, n, a, b)
        invariant forall j :: 0 <= j < i ==> 
            var (k, n, a, b) := queries[j];
            ValidResult(results[j], k, n, a, b)
    {
        var query := queries[i];
        var k, n, a, b := query.0, query.1, query.2, query.3;
        
        var result := -1;
        if n * b < k {
            var diff := a - b;
            var available := k - n * b - 1;
            var maxA := available / diff;
            if maxA >= n {
                result := n;
            } else {
                result := maxA;
            }
        }
        
        results := results + [result];
        i := i + 1;
    }
}
// </vc-code>

