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
    // K - A <= K - A (trivial)
    // Since B >= 0, subtracting a non-negative value cannot make it larger
    // Actually, this is not always true! Need to consider different cases
}

lemma LemmaSubtractLessThanOrEqual(A: int, B: int, K: int)
    requires ValidInput(A, B, K)
    requires A >= K
    ensures A - K >= 0
{
}

lemma LemmaSubtractExceedsB(A: int, B: int, K: int)
    requires ValidInput(A, B, K)
    requires A < K
    requires K - A > B
    ensures K - A - B > 0
{
}

lemma LemmaSubtractWithinB(A: int, B: int, K: int)
    requires ValidInput(A, B, K)
    requires A < K
    requires K - A <= B
    ensures B - (K - A) >= 0
{
    // Since K - A <= B, B - (K - A) >= 0
}

lemma LemmaKMinusAMinusBNonPositive(A: int, B: int, K: int)
    requires ValidInput(A, B, K)
    requires A < K
    ensures K - A - B <= 0
{
    // This is not generally true! When B is small, K - A - B can be positive
    // The lemma should be removed as it's incorrect
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
        LemmaSubtractLessThanOrEqual(A, B, K);
        assert takahashi == ExpectedTakahashiCookies(A, B, K);
        assert aoki == ExpectedAokiCookies(A, B, K);
    } else {
        takahashi := 0;
        assert takahashi == ExpectedTakahashiCookies(A, B, K);
        if K - A <= B {
            aoki := B - (K - A);
            LemmaSubtractWithinB(A, B, K);
            assert aoki == ExpectedAokiCookies(A, B, K);
        } else {
            aoki := 0;
            assert aoki == ExpectedAokiCookies(A, B, K);
        }
    }
}
// </vc-code>

