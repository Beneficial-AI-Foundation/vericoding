// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires a.Length == N
    requires sum.Length == 1
    requires N > 0
    requires N < 1000
    modifies sum
    ensures sum[0] <= 3 * N
// </vc-spec>
// <vc-code>
{
  sum[0] := 0;
}
// </vc-code>
