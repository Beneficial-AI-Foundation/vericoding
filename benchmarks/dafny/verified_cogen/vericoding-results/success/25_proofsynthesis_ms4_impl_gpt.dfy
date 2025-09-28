// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function threeN(n: int): int { 3 * n }
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
{
  sum[0] := 0;
}
// </vc-code>
