// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsUniqueAndSorted(s: seq<nat>): bool {
    forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
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
/* code modified by LLM (iteration 2): implement nonzero method */
{
  var result_indices: seq<nat> := [];
  var i: nat := 0;

  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < |result_indices| ==> result_indices[k] < |a| && a[result_indices[k]] != 0.0
    invariant forall k :: 0 <= k < i && a[k] != 0.0 ==> k in result_indices
    invariant forall k, l :: 0 <= k < l < |result_indices| ==> result_indices[k] < result_indices[l]
    invariant forall k :: 0 <= k < |result_indices| ==> result_indices[k] < i // All collected indices are from processed part of 'a'
  {
    if a[i] != 0.0 {
      result_indices := result_indices + [i];
    }
    i := i + 1;
  }
  indices := result_indices;
}
// </vc-code>
