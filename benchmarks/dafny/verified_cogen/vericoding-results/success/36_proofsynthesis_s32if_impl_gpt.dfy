// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function fourTimes(n: int): int { 4 * n }
// </vc-helpers>

// <vc-spec>
method MyFun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1 &&
		N < 1000
	modifies a, sum
	ensures
		sum[0] == 4 * N
// </vc-spec>
// <vc-code>
{
  sum[0] := 4 * N;
}
// </vc-code>
