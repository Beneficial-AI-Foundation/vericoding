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
	modifies sum
	ensures
		sum[0] == 3 * N
// </vc-spec>
// <vc-code>
{
  var i: int := 0;
  var s: int := 0;
  while i < N
    invariant 0 <= i <= N
    invariant s == 3 * i
  {
    s := s + 3;
    i := i + 1;
  }
  sum[0] := s;
}
// </vc-code>
