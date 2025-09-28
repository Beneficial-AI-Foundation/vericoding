// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function FiveTimes(n: int): int { 5 * n }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
    requires 
        a.Length == N &&
        sum.Length == 1 &&
        N > 0 &&
        N < 1000
    ensures
        sum[0] <= 5 * N
    modifies a, sum
// </vc-spec>
// <vc-code>
{
  sum[0] := FiveTimes(N);
}
// </vc-code>
