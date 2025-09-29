// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  var i := 0;
  sum[0] := 0;
  while i < N
    invariant 0 <= i <= N
    invariant sum[0] == i
  {
    sum[0] := sum[0] + 1;
    i := i + 1;
  }
}
// </vc-code>
