// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, sum: array<int>, N: int)
	requires N > 0
	requires a.Length == N
	requires sum.Length == 1
	ensures forall k :: 0 <= k < N ==> a[k] == 0
	modifies a, sum
// </vc-spec>
// <vc-code>
{
  var i := 0;
  sum[0] := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall k :: 0 <= k < i ==> a[k] == 0
  {
    a[i] := 0;
    sum[0] := sum[0] + a[i];
    i := i + 1;
  }
}
// </vc-code>
