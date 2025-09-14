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
lemma ExpectedTakahashiCookiesLemma(A: int, B: int, K: int)
    requires ValidInput(A, B, K)
    ensures (A >= K ==> ExpectedTakahashiCookies(A, B, K) == A - K) &&
            (A < K ==> ExpectedTakahashiCookies(A, B, K) == 0)
{
}

lemma ExpectedAokiCookiesLemma(A: int, B: int, K: int)
    requires ValidInput(A, B, K)
    ensures (A >= K ==> ExpectedAokiCookies(A, B, K) == B) &&
            (A < K && K - A < B ==> ExpectedAokiCookies(A, B, K) == B - (K - A)) &&
            (A < K && K - A >= B ==> ExpectedAokiCookies(A, B, K) == 0)
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
    var new_takahashi: int;
    var new_aoki: int;

    ExpectedTakahashiCookiesLemma(A, B, K);
    ExpectedAokiCookiesLemma(A, B, K);

    if A >= K {
        new_takahashi := A - K;
        new_aoki := B;
    } else {
        new_takahashi := 0;
        var remaining_K := K - A;
        if remaining_K < B {
            new_aoki := B - remaining_K;
        } else {
            new_aoki := 0;
        }
    }

    takahashi := new_takahashi;
    aoki := new_aoki;
}
// </vc-code>

