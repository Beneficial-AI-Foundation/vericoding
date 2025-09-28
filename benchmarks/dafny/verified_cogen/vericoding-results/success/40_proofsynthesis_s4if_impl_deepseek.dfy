// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ComputeSum(q: array<int>, n: int): int
  requires n >= 0 && q.Length >= n
  ensures ComputeSum(q, n) == 4 * n
{
  if n == 0 then
    0
  else
    ComputeSum(q, n - 1) + 4
}
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    requires N < 1000
    modifies sum
    ensures sum[0] == 4 * N
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed array slice issue and recursive computation */
{
  sum[0] := ComputeSum(a, N);
}
// </vc-code>
