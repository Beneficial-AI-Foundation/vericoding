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
lemma MaxActionATurns_returns_valid(k: int, n: int, a: int, b: int)
    requires ValidQuery(k, n, a, b)
    ensures ValidResult(MaxActionATurns(k, n, a, b), k, n, a, b)
{
    reveal MaxActionATurns;
    if n * b > k {
        assert MaxActionATurns(k, n, a, b) == -1;
    } else {
        var maxPossible := (k - n * b - 1) / (a - b);
        if n <= maxPossible {
            assert MaxActionATurns(k, n, a, b) == n;
            assert 0 <= n <= n;
        } else {
            assert MaxActionATurns(k, n, a, b) == maxPossible;
            if maxPossible < 0 {
                // Since n * b <= k, we have k - n*b >= 0, so (k - n*b - 1) >= -1.
                var num := k - n * b - 1;
                assert num >= -1;
                assert num < 0;
                assert num == -1;
                // For positive divisor (a - b) > 0 and numerator -1, division yields -1.
                assert maxPossible == -1;
            } else {
                assert 0 <= maxPossible <= n;
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
    var res := [];
    var i := 0;
    while i < |queries|
        invariant 0 <= i <= |queries|
        invariant |res| == i
        invariant forall j :: 0 <= j < i ==>
            res[j] == MaxActionATurns(queries[j].0, queries[j].1, queries[j].2, queries[j].3)
        invariant forall j :: 0 <= j < i ==>
            ValidResult(res[j], queries[j].0, queries[j].1, queries[j].2, queries[j].3)
    {
        var q := queries[i];
        var k := q.0;
        var n := q.1;
        var a := q.2;
        var b := q.3;
        var r := MaxActionATurns(k, n, a, b);
        // use lemma to establish validity for this query/result
        MaxActionATurns_returns_valid(k, n, a, b);
        res := res + [r];
        i := i + 1;
    }
    results := res;
}
// </vc-code>

