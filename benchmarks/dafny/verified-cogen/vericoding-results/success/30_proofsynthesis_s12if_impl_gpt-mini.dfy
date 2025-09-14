// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Double(n: int): int { 2 * n }
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
{
  sum[0] := Double(N);
}
// </vc-code>
