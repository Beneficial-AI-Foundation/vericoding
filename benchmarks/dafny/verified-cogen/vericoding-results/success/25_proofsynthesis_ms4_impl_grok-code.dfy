// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added clamping function to cap contributions between 0 and 3 */
function toClamp(n: int): int { if n < 0 then 0 else if n <= 3 then n else 3 }
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
		sum[0] <= 3 * N
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): updated loop with clamping and loop invariant */
{
  sum[0] := 0;
  for i := 0 to N - 1
    invariant 0 <= i <= N
    invariant sum[0] <= 3 * i
  {
    sum[0] := sum[0] + toClamp(a[i]);
  }
}
// </vc-code>
