// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function twice(x: int): int { 2 * x }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1 &&
		N < 1000

	ensures
		sum[0] == 2 * N

	modifies a, sum
// </vc-spec>
// <vc-code>
{
  sum[0] := twice(N);
}
// </vc-code>
