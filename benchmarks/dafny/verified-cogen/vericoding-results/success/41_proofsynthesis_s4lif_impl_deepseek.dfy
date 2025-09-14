// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Add decreases clause to recursive function */
function SumFunction(start: int, end: int): int
  requires 0 <= start <= end
  ensures SumFunction(start, end) == 5 * (end - start)
  decreases end - start
{
  if start == end then 0 else 5 + SumFunction(start + 1, end)
}
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    requires sum.Length == 1
    requires N < 1000
    modifies sum
    ensures sum[0] == 5 * N
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Use correct implementation */
{
  sum[0] := 5 * N;
}
// </vc-code>
