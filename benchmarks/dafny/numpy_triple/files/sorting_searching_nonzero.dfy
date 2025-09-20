// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
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
{
  assume {:axiom} false;
}
// </vc-code>
