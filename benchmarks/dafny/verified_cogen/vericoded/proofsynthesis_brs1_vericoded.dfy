// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MyFun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    modifies a, sum
    ensures sum[0] <= N
// </vc-spec>
// <vc-code>
{
  var total := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant total <= i
  {
    if a[i] > 0 {
      total := total + 1;
    }
    a[i] := 0;
    i := i + 1;
  }
  sum[0] := total;
}
// </vc-code>
