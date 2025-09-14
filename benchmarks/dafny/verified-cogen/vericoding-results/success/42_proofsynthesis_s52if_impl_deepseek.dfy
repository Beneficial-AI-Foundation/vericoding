// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SumHelper(n: int): int
  requires n >= 0
  ensures SumHelper(n) == 6 * n
{
  if n == 0 then 0 else 6 + SumHelper(n - 1)
 }

/* helper modified by LLM (iteration 2): Fixed SumHelper to correctly calculate 6*n through recursion and simple arithmetic */
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    requires N < 1000
    modifies sum
    ensures sum[0] == 6 * N
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Simple loop to accumulate 6*N in sum[0] */
  sum[0] := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sum[0] == 6 * i
  {
    sum[0] := sum[0] + 6;
    i := i + 1;
  }
  assert sum[0] == 6 * N;
}
// </vc-code>
