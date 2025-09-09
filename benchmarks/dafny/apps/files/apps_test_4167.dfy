Count ordered triples (a,b,c) where 1 ≤ a,b,c ≤ N and a+b, b+c, c+a are all divisible by K

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

method solve(N: int, K: int) returns (result: int)
    requires ValidInput(N, K)
    ensures result >= 0
    ensures result == CountValidTriples(N, K)
{
    var cnt1 := 0;
    var cnt2 := 0;

    // Count numbers from 1 to N that are divisible by K
    var i := 1;
    while i <= N
        invariant 1 <= i <= N + 1
        invariant cnt1 == CountDivisibleByK(i - 1, K)
        invariant cnt1 >= 0
    {
        if i % K == 0 {
            cnt1 := cnt1 + 1;
        }
        i := i + 1;
    }

    assert cnt1 == N / K;

    if K % 2 == 1 {
        // If K is odd, only consider numbers divisible by K
        result := cnt1 * cnt1 * cnt1;
    } else {
        // If K is even, also count numbers with remainder K/2
        i := 1;
        while i <= N
            invariant 1 <= i <= N + 1
            invariant cnt2 == CountWithRemainderHalfK(i - 1, K)
            invariant cnt2 >= 0
        {
            if i % K == 0 || i % K == K / 2 {
                cnt2 := cnt2 + 1;
            }
            i := i + 1;
        }

        assert cnt2 == N / K + (if N % K >= K / 2 then 1 else 0);
        result := cnt1 * cnt1 * cnt1 + cnt2 * cnt2 * cnt2;
    }
}
