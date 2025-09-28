// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function times4(x: int): int { 4 * x }
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
  sum[0] := times4(N);
}
// </vc-code>
