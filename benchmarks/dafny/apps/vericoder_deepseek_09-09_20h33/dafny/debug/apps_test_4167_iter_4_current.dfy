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
lemma CountDivisibleByK_Mod2(n: int, K: int)
    requires K >= 1
    ensures CountDivisibleByK(n, K) == n / K
{
    // Proof is trivial by function definition
}

lemma CountWithRemainderHalfK_Mod2(n: int, K: int)
    requires K >= 1
    ensures CountWithRemainderHalfK(n, K) == n / K + (if n % K >= K / 2 then 1 else 0)
{
    // Proof is trivial by function definition
}

lemma CountValidTriples_OddCase(N: int, K: int)
    requires N >= 1 && K >= 1 && K % 2 == 1
    ensures CountValidTriples(N, K) == (N / K) * (N / K) * (N / K)
{
    // Proof follows from function definition
}

lemma CountValidTriples_EvenCase(N: int, K: int)
    requires N >= 1 && K >= 1 && K % 2 == 0
    ensures CountValidTriples(N, K) == 
        (N / K) * (N / K) * (N / K) + 
        ((N / K) + (if N % K >= K / 2 then 1 else 0)) * 
        ((N / K) + (if N % K >= K / 2 then 1 else 0)) * 
        ((N / K) + (if N % K >= K / 2 then 1 else 0))
{
    // Proof follows from function definition
}

lemma ValidInputImpliesNonNegativeDiv(N: int, K: int)
    requires ValidInput(N, K)
    ensures N / K >= 0
{
    // Since N >= 1 and K >= 1, division is non-negative
}

ghost function CountDivisibleByKImpl(n: int, K: int): int
    requires K >= 1
{
    n / K
}

ghost function CountWithRemainderHalfKImpl(n: int, K: int): int
    requires K >= 1
{
    n / K + (if n % K >= K / 2 then 1 else 0)
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
        assert result == CountValidTriples(N, K) by {
            CountValidTriples_OddCase(N, K);
        }
    } else {
        var cnt1 := N / K;
        var halfK := K / 2;
        var rem := N % K;
        var cnt2 := cnt1 + (if rem >= halfK then 1 else 0);
        result := cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2;
        assert result == CountValidTriples(N, K) by {
            CountValidTriples_EvenCase(N, K);
        }
    }
}
// </vc-code>

