// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function times6(n: int): int { 6 * n }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1 &&
		N < 1000

	ensures
		sum[0] == 6 * N
	modifies a, sum
// </vc-spec>
// <vc-code>
{
  sum[0] := times6(N);
}
// </vc-code>
