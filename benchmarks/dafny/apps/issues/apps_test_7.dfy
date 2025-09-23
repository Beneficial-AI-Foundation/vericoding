// <vc-preamble>
predicate ValidInput(n: int, m: int) {
    1 <= n <= 1000000000000000000 && 1 <= m <= 1000000000000000000
}

function TriangularSum(k: int): int 
    requires k >= 0
{
    (1 + k) * k / 2
}

predicate CorrectResultWhenMGeqN(n: int, m: int, result: int) {
    m >= n ==> result == n
}

predicate CorrectResultWhenMLtN(n: int, m: int, result: int) {
    m < n ==> (
        exists r: int :: r >= 0 && 
        TriangularSum(r) >= n - m &&
        (r == 0 || TriangularSum(r-1) < n - m) &&
        result == r + m
    )
}

predicate ValidResult(result: int) {
    result >= 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
    requires ValidInput(n, m)
    ensures ValidResult(result)
    ensures CorrectResultWhenMGeqN(n, m, result)
    ensures CorrectResultWhenMLtN(n, m, result)
// </vc-spec>
// <vc-code>
{
    if m >= n {
        result := n;
    } else {
        var c := n - m;
        var l := 0;
        var r := 1000000000000000000;

        while r - l > 1
            invariant 0 <= l < r
            invariant l == 0 || TriangularSum(l) < c
            invariant TriangularSum(r) >= c
        {
            var md := (r + l) / 2;
            if TriangularSum(md) < c {
                l := md;
            } else {
                r := md;
            }
        }

        assert r >= 0;
        assert TriangularSum(r) >= c;
        assert r == 0 || TriangularSum(r-1) < c;
        assert r + m >= 1;

        result := r + m;
    }
}
// </vc-code>
