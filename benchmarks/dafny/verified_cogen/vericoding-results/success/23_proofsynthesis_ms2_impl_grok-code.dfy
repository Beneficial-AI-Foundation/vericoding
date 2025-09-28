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
  var s := 0;
  for i := 0 to N-1 {
    s := s + a[i];
  }
  sum[0] := min(s, N);
}
// </vc-code>
