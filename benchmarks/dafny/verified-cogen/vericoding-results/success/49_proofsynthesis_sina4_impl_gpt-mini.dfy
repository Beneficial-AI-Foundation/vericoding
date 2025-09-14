// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): ensures N is within array bounds and all entries match v */
predicate AllBSet(b: array<int>, N: int, v: int)
  reads b
{
  0 <= N <= b.Length && forall k :: 0 <= k < N ==> b[k] == v
}
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, b: array<int>, sum: array<int>, N: int)
	requires N > 0
	requires a.Length == N
	requires b.Length == N
	requires sum.Length == 1
	requires N < 1000
	ensures forall k :: 0 <= k < N ==> b[k] == N + 2
	modifies a, b, sum
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): set all elements of b to N+2 using loop */
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant AllBSet(b, i, N + 2)
    decreases N - i
  {
    b[i] := N + 2;
    i := i + 1;
  }
}
// </vc-code>
