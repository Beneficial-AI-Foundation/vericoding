// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
predicate Nonneg(x: int) { x >= 0 }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
	requires a.Length == N && sum.Length == 1 && N > 0
	modifies a, sum
	ensures sum[0] <= N
// </vc-spec>
// <vc-code>
{
  sum[0] := 0;
}
// </vc-code>
