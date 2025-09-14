// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int) 
	requires a.Length == N && sum.Length == 1 && N > 0
	modifies a, sum
	ensures sum[0] <= N
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var s := 0;
  while i < N 
    invariant 0 <= i <= N
    invariant s <= i
  {
    s := min(s + a[i], i + 1);
    i := i + 1;
  }
  sum[0] := s;
}
// </vc-code>
