// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function fiveTimes(n: int): int { 5 * n }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    requires N < 1000
    ensures sum[0] == 5 * N
    modifies a, sum
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < N
    {
        a[i] := 0;
        i := i + 1;
    }
    sum[0] := fiveTimes(N);
}
// </vc-code>
