// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function FourTimes(N: int): int { 4 * N }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
    requires 
        a.Length == N &&
        sum.Length == 1 &&
        N > 0 &&
        N < 1000
    ensures
        sum[0] <= 4 * N
    modifies a, sum
// </vc-spec>
// <vc-code>
{
  sum[0] := 0;
}
// </vc-code>
