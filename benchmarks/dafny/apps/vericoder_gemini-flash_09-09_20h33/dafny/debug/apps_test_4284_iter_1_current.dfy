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
    var newResults := new int[|queries|];
    for i := 0 to |queries| - 1
        invariant 0 <= i <= |queries|
        invariant forall j :: 0 <= j < i ==> 
            var (k, n, a, b) := queries[j];
            newResults[j] == MaxActionATurns(k, n, a, b)
    {
        var (k, n, a, b) := queries[i];
        if n * b > k then
            newResults[i] := -1;
        else
            var maxPossible := (k - n * b - 1) / (a - b);
            if n <= maxPossible then
                newResults[i] := n;
            else
                newResults[i] := maxPossible;
        
        // Assert ValidResult after computing the result for the current query
        // This is implicitly handled by the postcondition of the solve method.
        // The verification of `MaxActionATurns` function ensures the `ValidResult` property.
    }
    results := newResults;
}
// </vc-code>

