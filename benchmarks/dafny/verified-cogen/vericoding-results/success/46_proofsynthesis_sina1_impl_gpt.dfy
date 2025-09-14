// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate InRange(i: int, N: int) { 0 <= i < N }
function Id(x: int): int { x }
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
    invariant forall k:int :: 0 <= k < i ==> a[k] == N
    decreases N - i
  {
    a[i] := N;
    i := i + 1;
  }
}
// </vc-code>
