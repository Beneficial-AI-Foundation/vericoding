// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1 &&
		N < 1000

	ensures
		sum[0] == 6 * N
	modifies a, sum
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var s := 0;
  while i < N
    invariant 0 <= i <= N
    invariant s == 6 * i
    decreases N - i
  {
    a[i] := 6;
    s := s + 6;
    i := i + 1;
  }
  sum[0] := s;
}
// </vc-code>
