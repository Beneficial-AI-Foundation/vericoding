// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma HelperLemma(n: int)
  requires n >= 0
  ensures 5 * n == n + n + n + n + n
{
}

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
  /* code modified by LLM (iteration 2): Fixed loop invariant and array update logic */
  var i := 0;
  sum[0] := 0;
  
  while i < N
    invariant 0 <= i <= N
    invariant sum[0] == 5 * i
  {
    sum[0] := sum[0] + 5;
    i := i + 1;
  }
}
// </vc-code>
