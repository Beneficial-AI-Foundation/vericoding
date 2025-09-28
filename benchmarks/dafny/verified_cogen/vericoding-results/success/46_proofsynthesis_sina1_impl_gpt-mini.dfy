// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): predicate to express that all elements of an array equal a given value */
predicate ArrayAllEquals(a: array<int>, v: int) reads a { forall i :: 0 <= i < a.Length ==> a[i] == v }
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
  /* code modified by LLM (iteration 3): set all elements of a to N while handling potential aliasing with sum */
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall k :: 0 <= k < i ==> a[k] == N
    decreases N - i
  {
    a[i] := N;
    i := i + 1;
  }
  assert i == N;
  assert forall k :: 0 <= k < N ==> a[k] == N;
  if sum == a {
    sum[0] := N;
  } else {
    sum[0] := 0;
  }
}
// </vc-code>
