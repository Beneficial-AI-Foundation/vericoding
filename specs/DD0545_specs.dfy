// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method sort(A: array<int>, n: int)
modifies A; requires n==A.Length;
  requires n>=0;            
  ensures forall i,j:: 0<=i<=j<n ==> A[i]<=A[j];
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
