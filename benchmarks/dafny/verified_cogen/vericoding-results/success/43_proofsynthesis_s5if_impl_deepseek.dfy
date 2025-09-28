// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added decreases clause to fix termination proof */
lemma HelperLemma(i: int, n: int)
  requires n >= 0
  requires i >= 0
  ensures 5 * i + 5 * (n - i) == 5 * n
  decreases n - i
{
  if i < n {
    HelperLemma(i + 1, n);
  }
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
/* code modified by LLM (iteration 3): No changes needed to code section, helper lemma fixed */
{
  var i := 0;
  sum[0] := 0;
  
  while i < N
    invariant 0 <= i <= N
    invariant sum[0] == 5 * i
    decreases N - i
  {
    sum[0] := sum[0] + 5;
    i := i + 1;
  }
  
  HelperLemma(i, N);
}
// </vc-code>
