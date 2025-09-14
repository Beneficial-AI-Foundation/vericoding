// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
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
  /* code modified by LLM (iteration 2): changed array assignments to ensure invariant holds */
  sum[0] := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sum[0] <= 3 * i
  {
    a[i] := 0;
    b[i] := 0;
    c[i] := 0;
    sum[0] := sum[0] + a[i] + b[i] + c[i];
    i := i + 1;
  }
}
// </vc-code>
