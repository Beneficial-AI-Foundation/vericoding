predicate ValidTriple(a: int, b: int, c: int, N: int, K: int)
    requires K >= 1
{
    1 <= a <= N && 1 <= b <= N && 1 <= c <= N &&
    (a + b) % K == 0 && (b + c) % K == 0 && (c + a) % K == 0
}

function CountValidTriples(N: int, K: int): int
    requires N >= 1 && K >= 1
{
    if K % 2 == 1 then
        var cnt1 := N / K;
        cnt1 * cnt1 * cnt1
    else
        var cnt1 := N / K;
        var cnt2 := N / K + (if N % K >= K / 2 then 1 else 0);
        cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2
}

predicate ValidInput(N: int, K: int)
{
    N >= 1 && K >= 1
}

function CountDivisibleByK(n: int, K: int): int
    requires K >= 1
{
    if n <= 0 then 0 else n / K
}

function CountWithRemainderHalfK(n: int, K: int): int
    requires K >= 1
{
    if n <= 0 then 0 else n / K + (if n % K >= K / 2 then 1 else 0)
}

// <vc-helpers>
lemma CountValidTriplesCorrect(N: int, K: int)
    requires N >= 1 && K >= 1
    ensures CountValidTriples(N, K) >= 0
{
    if K % 2 == 1 {
        var cnt1 := N / K;
        assert cnt1 >= 0;
        assert cnt1 * cnt1 * cnt1 >= 0;
    } else {
        var cnt1 := N / K;
        var cnt2 := N / K + (if N % K >= K / 2 then 1 else 0);
        assert cnt1 >= 0;
        assert cnt2 >= 0;
        assert cnt1 * cnt1 * cnt1 >= 0;
        assert cnt2 * cnt2 * cnt2 >= 0;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, K: int) returns (result: int)
    requires ValidInput(N, K)
    ensures result >= 0
    ensures result == CountValidTriples(N, K)
// </vc-spec>
// <vc-code>
{
    if K % 2 == 1 {
        var cnt1 := N / K;
        result := cnt1 * cnt1 * cnt1;
    } else {
        var cnt1 := N / K;
        var cnt2 := N / K + (if N % K >= K / 2 then 1 else 0);
        result := cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2;
    }
    CountValidTriplesCorrect(N, K);
}
// </vc-code>

