// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MyFun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1 &&
		N < 1000
	modifies a, sum
	ensures
		sum[0] == 4 * N
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed loop invariant by ensuring sum[0] is properly initialized and maintained */
  var i := 0;
  sum[0] := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sum[0] == 4 * i
  {
    sum[0] := sum[0] + 4;
    a[i] := 4;
    i := i + 1;
  }
}
// </vc-code>
