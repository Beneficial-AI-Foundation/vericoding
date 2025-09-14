// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Twice(n: int): int { 2 * n }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    requires N < 1000
    modifies a, sum
    ensures sum[0] == 2 * N
// </vc-spec>
// <vc-code>
{
  sum[0] := Twice(N);
}
// </vc-code>
