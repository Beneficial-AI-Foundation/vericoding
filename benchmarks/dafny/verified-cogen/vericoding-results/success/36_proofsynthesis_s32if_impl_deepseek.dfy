// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma SumLemma(n: int)
  requires 0 <= n < 1000
  ensures n + n + n + n == 4 * n
{
  /* helper modified by LLM (iteration 2): Base case at 0, recursive case */
  if n == 0 {
  } else {
    SumLemma(n - 1);
  }
}
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
  /* code modified by LLM (iteration 2): Initialize sum before loop */
  var i := 0;
  sum[0] := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sum[0] == 4 * i
  {
    a[i] := 0;
    sum[0] := sum[0] + 4;
    i := i + 1;
  }
  SumLemma(N);
}
// </vc-code>
