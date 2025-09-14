// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  var total := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant total <= 5 * i
  {
    if a[i] <= 5 {
      total := total + a[i];
    } else {
      total := total + 5;
    }
    i := i + 1;
  }
  sum[0] := total;
}
// </vc-code>
