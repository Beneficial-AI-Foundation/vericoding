// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause and bounds on upto to avoid out-of-range */
predicate PrefixParity(a: array<int>, n: int, upto: int) reads a { 0 <= upto <= a.Length && forall k:int :: 0 <= k < upto ==> a[k] % 2 == n % 2 }
// </vc-helpers>

// <vc-spec>
method myfun(a: array<int>, N: int)
    requires N > 0
    requires a.Length == N
    ensures forall k:int :: 0 <= k < N ==> a[k] % 2 == N % 2
    modifies a
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented loop filling array with N ensuring parity */
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant PrefixParity(a, N, i)
  {
    a[i] := N;
    i := i + 1;
  }
}

// </vc-code>
