// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Twice(n: int): int { n + n }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, b: array<int>, sum: array<int>, N: int)
	requires N > 0
	requires a.Length == N
	requires b.Length == N
	requires sum.Length == 1
	requires N < 1000
	ensures sum[0] <= 2 * N
	modifies a, b, sum
// </vc-spec>
// <vc-code>
{
  sum[0] := 2 * N;
}
// </vc-code>
