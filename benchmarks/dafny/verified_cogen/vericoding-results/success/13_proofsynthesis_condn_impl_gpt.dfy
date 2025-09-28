// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate InRange(k: int, n: int) { 0 <= k < n }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, N: int, m: int)
	requires N > 0
	requires a.Length == N
	modifies a
	ensures forall k :: 0 <= k < N ==> a[k] <= N
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant a.Length == N
    invariant forall k | 0 <= k < i :: a[k] == N
    decreases N - i
  {
    a[i] := N;
    i := i + 1;
  }
}
// </vc-code>
