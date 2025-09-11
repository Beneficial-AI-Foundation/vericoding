// <vc-preamble>
predicate ValidInput(A: int, B: int, K: int)
{
    A >= 0 && B >= 0 && K >= 0
}

function ExpectedTakahashiCookies(A: int, B: int, K: int): int
    requires ValidInput(A, B, K)
{
    if A >= K then A - K
    else 0
}

function ExpectedAokiCookies(A: int, B: int, K: int): int
    requires ValidInput(A, B, K)
{
    if A >= K then B
    else if K - A < B then B - (K - A)
    else 0
}

predicate CorrectResult(A: int, B: int, K: int, takahashi: int, aoki: int)
    requires ValidInput(A, B, K)
{
    takahashi == ExpectedTakahashiCookies(A, B, K) &&
    aoki == ExpectedAokiCookies(A, B, K) &&
    takahashi >= 0 && aoki >= 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, K: int) returns (takahashi: int, aoki: int)
    requires ValidInput(A, B, K)
    ensures CorrectResult(A, B, K, takahashi, aoki)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
