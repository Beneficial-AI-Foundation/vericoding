// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added `reads a` clause to allow reading array elements */
function SumArraySlice(a: array<int>, start: int, end: int): int
  requires 0 <= start <= end <= a.Length
  reads a
  decreases end - start
{
  if start == end then 0 else a[start] + SumArraySlice(a, start + 1, end)
}
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1 &&
		N < 1000
	modifies sum
	ensures
		sum[0] == 2 * N
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): no changes as the error was in the helper function */
{
  var i := 0;
  var current_sum := 0;
  while i < N
    invariant 0 <= i <= N
    invariant current_sum == 2 * i
  {
    current_sum := current_sum + 2;
    i := i + 1;
  }
  sum[0] := current_sum;
}
// </vc-code>
