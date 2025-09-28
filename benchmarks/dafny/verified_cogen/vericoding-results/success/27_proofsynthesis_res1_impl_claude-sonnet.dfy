// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, b: array<int>, sum: array<int>, N: int)
	requires N > 0
	requires a.Length == N
	requires b.Length == N
	requires sum.Length == 1
	requires N < 1000
	ensures sum[0] <= 2 * N
	modifies a, b, sum
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var total := 0;
  while i < N
    invariant 0 <= i <= N
    invariant total <= 2 * i
  {
    if a[i] >= 0 && a[i] <= 1 {
      total := total + a[i];
    }
    if b[i] >= 0 && b[i] <= 1 {
      total := total + b[i];
    }
    i := i + 1;
  }
  sum[0] := total;
}
// </vc-code>
