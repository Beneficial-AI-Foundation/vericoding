// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Id(n: int): int { n }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1
	modifies a, sum
	ensures
		sum[0] == N
// </vc-spec>
// <vc-code>
{
  sum[0] := N;
}
// </vc-code>
