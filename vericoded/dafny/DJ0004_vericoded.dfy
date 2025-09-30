// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  var total := 0;
  var i := 0;
  while (i < N)
    invariant 0 <= i <= N
    invariant total <= 3 * i
  {
    if (a[i] <= 3) {
      total := total + a[i];
    } else {
      total := total + 3;
    }
    i := i + 1;
  }
  sum[0] := total;
}
// </vc-code>
