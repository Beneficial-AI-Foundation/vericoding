// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Replaced 'result' with function name in 'ensures' clause to fix compilation error. */
function ComputeSum(n: int): int
  requires n > 0
  ensures ComputeSum(n) <= 2 * n
{
  n
}
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
    requires 
        a.Length == N &&
        sum.Length == 1 &&
        N > 0 &&
        N < 1000
    modifies sum
    ensures
        sum[0] <= 2 * N
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): No logic change; this code is now correct due to the fixed helper function. */
  sum[0] := ComputeSum(N);
}
// </vc-code>
