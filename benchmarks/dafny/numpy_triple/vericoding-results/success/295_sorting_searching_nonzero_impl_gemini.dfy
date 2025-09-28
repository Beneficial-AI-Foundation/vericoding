// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [rewrote quantifier to be over sequence indices to aid verifier] */
predicate IsPartialResult(indices: seq<nat>, a: seq<real>, i: int)
  requires 0 <= i <= |a|
{
  (forall p :: 0 <= p < |indices| ==> indices[p] < i && a[indices[p]] != 0.0) &&
  (forall j :: 0 <= j < i && a[j] != 0.0 ==> j in indices) &&
  (forall k1, k2 :: 0 <= k1 < k2 < |indices| ==> indices[k1] < indices[k2])
}
// </vc-helpers>

// <vc-spec>
method nonzero(a: seq<real>) returns (indices: seq<nat>)
  // No preconditions - accepts any sequence
  requires true
  // Every returned index must be valid and correspond to a non-zero element
  ensures forall i :: i in indices ==> i < |a| && a[i] != 0.0
  // Every non-zero element must have its index in the result (completeness)
  ensures forall j :: 0 <= j < |a| && a[j] != 0.0 ==> j in indices
  // The indices are returned in ascending order
  ensures forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]
  // No duplicates in the result (implied by ascending order, but made explicit)
  ensures forall i, j :: 0 <= i < |indices| && 0 <= j < |indices| && i != j ==> indices[i] != indices[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): [no changes, implementation is correct] */
{
  indices := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant IsPartialResult(indices, a, i)
  {
    if a[i] != 0.0 {
      indices := indices + [i as nat];
    }
    i := i + 1;
  }
}
// </vc-code>
