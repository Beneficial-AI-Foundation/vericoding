// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Clamp(x: int): int { if x > 3 then 3 else if x < 0 then 0 else x }
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
  var total: int := 0;
  var i: int := 0;
  while i < N
    invariant 0 <= i <= N
    invariant total <= 3 * i
  {
    total := total + Clamp(a[i]);
    i := i + 1;
  }
  sum[0] := total;
}
// </vc-code>
