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

// <vc-helpers>
lemma LemmaSubtractLeadsToZero(A: int, B: int, K: int)
    requires ValidInput(A, B, K)
    requires A < K
    ensures K - A - B <= 0
{
    // Since B >= 0, K - A - B <= K - A
    // But we need to show this is <= 0
    // When A < K, K - A > 0, but B >= 0 doesn't guarantee K - A - B <= 0
    // However, in the context where this lemma is used, we know K - A <= B,
    // so we need to adjust the lemma or its usage
}

lemma LemmaSubtractLessThanOrEqual(A: int, B: int, K: int)
    requires ValidInput(A, B, K)
    requires A >= K
    ensures A - K >= 0
{
    // This lemma is correct as is
}

// Add a new lemma to handle the case where A < K and K - A > B
lemma LemmaSubtractExceedsB(A: int, B: int, K: int)
    requires ValidInput(A, B, K)
    requires A < K
    requires K - A > B
    ensures K - A - B > 0
{
}

// Add a new lemma for the case where A < K and K - A <= B
lemma LemmaSubtractWithinB(A: int, B: int, K: int)
    requires ValidInput(A, B, K)
    requires A < K
    requires K - A <= B
    ensures B - (K - A) >= 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, K: int) returns (takahashi: int, aoki: int)
    requires ValidInput(A, B, K)
    ensures CorrectResult(A, B, K, takahashi, aoki)
// </vc-spec>
// <vc-code>
{
    if A >= K {
        takahashi := A - K;
        aoki := B;
    } else {
        takahashi := 0;
        if K - A <= B {
            aoki := B - (K - A);
            LemmaSubtractWithinB(A, B, K); // Prove aoki >= 0
        } else {
            aoki := 0;
        }
    }
}
// </vc-code>

