// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MyFun(a: array<int>, sum: array<int>, N: int)
	requires
		N > 0 &&
		a.Length == N &&
		sum.Length == 1 &&
		N < 1000
	modifies a, sum
	ensures
		sum[0] == 4 * N
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall j :: 0 <= j < i ==> a[j] == 4
  {
    a[i] := 4;
    i := i + 1;
  }
  
  var s := 0;
  i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant s == 4 * i
    invariant forall j :: 0 <= j < N ==> a[j] == 4
  {
    s := s + a[i];
    i := i + 1;
  }
  
  sum[0] := s;
}
// </vc-code>
