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
/* code modified by LLM (iteration 5): Moved assignment to sum[0] to beginning to help verifier prove postcondition */
{
  sum[0] := 0;
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
