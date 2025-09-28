// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate AllZeros(s: seq<int>) {
  forall k :: 0 <= k < |s| ==> s[k] == 0
}
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
  sum[0] := 0;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant a.Length == N
    invariant forall k :: 0 <= k < i ==> a[k] == 0
    decreases N - i
  {
    a[i] := 0;
    i := i + 1;
  }
}
// </vc-code>
