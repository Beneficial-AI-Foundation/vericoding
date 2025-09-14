// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function multiplyByFour(n: int): int { 4 * n }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    requires N < 1000
    modifies sum
    ensures sum[0] == 4 * N
// </vc-spec>
// <vc-code>
{
  sum[0] := multiplyByFour(N);
}
// </vc-code>
