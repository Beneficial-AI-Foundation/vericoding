// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added reads clause to the CountPositive function to fix compilation error by allowing reading from the array 'a'. */
function CountPositive(a: array<int>, N: int): int
  requires 0 <= N <= a.Length
  ensures 0 <= CountPositive(a, N) <= N
  decreases N
  reads a
{
  if N == 0 then 0 else if a[N - 1] > 0 then 1 + CountPositive(a, N - 1) else CountPositive(a, N - 1)
}
// </vc-helpers>

// <vc-spec>
method MyFun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    modifies a, sum
    ensures sum[0] <= N
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Set sum[0] to the positive count from CountPositive function. */
{
  sum[0] := CountPositive(a, N);
}
// </vc-code>
