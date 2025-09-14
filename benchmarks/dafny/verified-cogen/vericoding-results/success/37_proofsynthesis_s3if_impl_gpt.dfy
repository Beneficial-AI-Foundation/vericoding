// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function triple(n: int): int { 3 * n }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    requires N < 1000
    modifies sum
    ensures sum[0] == 3 * N
// </vc-spec>
// <vc-code>
{
  sum[0] := triple(N);
}
// </vc-code>
