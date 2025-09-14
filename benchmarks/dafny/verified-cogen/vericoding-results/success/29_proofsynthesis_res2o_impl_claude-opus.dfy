// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, b: array<int>, c: array<int>, sum: array<int>, N: int)
	requires N > 0
	requires a.Length == N
	requires b.Length == N
	requires c.Length == N
	requires sum.Length == 1
	requires N < 1000
	ensures sum[0] <= 3 * N
	modifies a, b, c, sum
// </vc-spec>
// <vc-code>
{
  var i := 0;
  sum[0] := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sum[0] <= 3 * i
  {
    if a[i] <= b[i] && a[i] <= c[i] {
      a[i] := 1;
      b[i] := 0;
      c[i] := 0;
    } else if b[i] <= a[i] && b[i] <= c[i] {
      a[i] := 0;
      b[i] := 1;
      c[i] := 0;
    } else {
      a[i] := 0;
      b[i] := 0;
      c[i] := 1;
    }
    sum[0] := sum[0] + a[i] + b[i] + c[i];
    i := i + 1;
  }
}
// </vc-code>
