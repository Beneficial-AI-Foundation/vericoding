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
lemma MaxActionATurnsValidResult(k: int, n: int, a: int, b: int)
    requires ValidQuery(k, n, a, b)
    ensures ValidResult(MaxActionATurns(k, n, a, b), k, n, a, b)
{
    var result := MaxActionATurns(k, n, a, b);
    if n * b > k {
        assert result == -1;
    } else {
        var maxPossible := (k - n * b - 1) / (a - b);
        if n <= maxPossible {
            assert result == n;
            assert 0 <= result <= n;
        } else {
            assert result == maxPossible;
            // Need to prove maxPossible >= 0 when n > maxPossible
            if maxPossible < 0 {
                // If maxPossible < 0, then k - n * b - 1 < 0
                // This means k < n * b + 1
                // Since k >= n * b (we're in the else branch), we have n * b <= k < n * b + 1
                // This means k == n * b (since k is an integer)
                // So maxPossible = (n * b - n * b - 1) / (a - b) = -1 / (a - b)
                // Since a > b > 0, we have a - b >= 1, so maxPossible = -1 / (a - b) = -1
                // But we also have n > maxPossible = -1
                // Since n > 0, this is always true
                assert k - n * b - 1 < 0;
                assert k - n * b < 1;
                assert n * b <= k;
                assert k - n * b >= 0;
                assert 0 <= k - n * b < 1;
                assert k == n * b;
                assert maxPossible == -1 / (a - b);
                assert a - b >= 1;
                assert maxPossible == -1;
                assert n > 0;
                assert n > maxPossible;
                assert result == -1;
                assert ValidResult(result, k, n, a, b);
            } else {
                assert maxPossible >= 0;
                assert result == maxPossible;
                assert 0 <= result;
                assert n > maxPossible;
                assert result < n;
                assert result <= n;
            }
        }
    }
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
        invariant 0 <= i <= |queries|
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==> 
            var (k, n, a, b) := queries[j];
            results[j] == MaxActionATurns(k, n, a, b)
        invariant forall j :: 0 <= j < i ==>
            var (k, n, a, b) := queries[j];
            ValidResult(results[j], k, n, a, b)
    {
        var (k, n, a, b) := queries[i];
        assert ValidQuery(k, n, a, b);
        
        var result := MaxActionATurns(k, n, a, b);
        MaxActionATurnsValidResult(k, n, a, b);
        
        results := results + [result];
        i := i + 1;
    }
}
// </vc-code>

