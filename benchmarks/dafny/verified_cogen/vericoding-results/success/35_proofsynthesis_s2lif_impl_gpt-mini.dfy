// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function triple(x: int): int { 3 * x }
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
		sum[0] == 3 * N
// </vc-spec>
// <vc-code>
{
  sum[0] := triple(N);
}
// </vc-code>
