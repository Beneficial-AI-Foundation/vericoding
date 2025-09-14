// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added precondition to ensure array bounds */
predicate AllZero(a: array<int>, N: int) reads a
  requires 0 <= N <= a.Length
{
  forall k :: 0 <= k < N ==> a[k] == 0
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
  /* code modified by LLM (iteration 3): no changes needed */
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall k :: 0 <= k < i ==> a[k] == 0
  {
    a[i] := 0;
    i := i + 1;
  }
  sum[0] := 0;
}
// </vc-code>
