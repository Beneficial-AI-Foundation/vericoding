// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function times5(n: int): int { 5 * n }
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
  sum[0] := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sum[0] == 5 * i
  {
    sum[0] := sum[0] + 5;
    i := i + 1;
  }
}
// </vc-code>
