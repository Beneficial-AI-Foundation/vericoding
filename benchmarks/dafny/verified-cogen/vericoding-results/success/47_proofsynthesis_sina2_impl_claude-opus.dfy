// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires N > 0
	requires a.Length == N
	requires sum.Length == 1
	requires N < 1000
	modifies a, sum
	ensures forall k :: 0 <= k < N ==> a[k] == N + 1
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall k :: 0 <= k < i ==> a[k] == N + 1
  {
    a[i] := N + 1;
    i := i + 1;
  }
}
// </vc-code>
