// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ComputeResult(n: int, pos: int): int
  requires n >= 0 && pos >= 0
  ensures ComputeResult(n, pos) == 2 * n
{
  2 * n
}

lemma HelperLemma(n: int)
  ensures n + n == 2 * n
{
}

/* helper modified by LLM (iteration 2): Added loop invariant helper lemma */
lemma LoopInvariantLemma(sumValue: int, pos: int, n: int)
  requires 0 <= pos <= n
  ensures sumValue == 2 * pos ==> (sumValue + 2) == 2 * (pos + 1)
{
}
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1 &&
		N < 1000
	ensures
		sum[0] == 2 * N
	modifies a, sum
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed loop invariant with proper initialization */
  var pos := 0;
  sum[0] := 0;
  
  while pos < N
    invariant 0 <= pos <= N
    invariant sum[0] == 2 * pos
  {
    sum[0] := sum[0] + 2;
    pos := pos + 1;
  }
  
  HelperLemma(N);
}
// </vc-code>
