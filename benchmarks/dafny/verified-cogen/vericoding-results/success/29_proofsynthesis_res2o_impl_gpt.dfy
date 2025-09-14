// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function triple(n: int): int { 3 * n }
predicate NonNegTimes3(n: int) { n >= 0 ==> 0 <= 3 * n }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, b: array<int>, c: array<int>, sum: array<int>, N: int)
	requires N > 0
	requires a.Length == N
	requires b.Length == N
	requires c.Length == N
	requires sum.Length == 1
	requires N < 1000
	ensures sum[0] <= 3 * N
	modifies a, b, c, sum
// </vc-spec>
// <vc-code>
{
  sum[0] := 0;
}
// </vc-code>
