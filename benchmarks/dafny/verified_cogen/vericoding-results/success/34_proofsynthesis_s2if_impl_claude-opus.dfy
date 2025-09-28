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
		sum[0] == 2 * N
	modifies a, sum
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall j :: 0 <= j < i ==> a[j] == 2
    modifies a
  {
    a[i] := 2;
    i := i + 1;
  }
  
  var s := 0;
  i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant s == 2 * i
  {
    s := s + a[i];
    i := i + 1;
  }
  
  sum[0] := s;
}
// </vc-code>
