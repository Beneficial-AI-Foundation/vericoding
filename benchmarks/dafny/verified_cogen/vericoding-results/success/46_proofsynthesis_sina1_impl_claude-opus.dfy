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
		forall k:int :: 0 <= k < N ==> a[k] == N
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall k :: 0 <= k < i ==> a[k] == N
  {
    a[i] := N;
    i := i + 1;
  }
}
// </vc-code>
