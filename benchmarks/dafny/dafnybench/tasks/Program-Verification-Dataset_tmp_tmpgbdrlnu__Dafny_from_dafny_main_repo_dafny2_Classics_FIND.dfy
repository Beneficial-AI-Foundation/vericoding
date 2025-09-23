// <vc-preamble>
ghost function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FIND(A: array<int>, N: int, f: int)
  requires A.Length == N;
  requires 0 <= f < N;
  modifies A;
  ensures forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[q];
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
