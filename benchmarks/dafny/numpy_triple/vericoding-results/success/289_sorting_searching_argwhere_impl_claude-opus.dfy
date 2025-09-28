// <vc-preamble>
// Method to find indices of non-zero elements in a sequence
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method numpy_argwhere(a: seq<real>) returns (indices: seq<nat>)
  // No preconditions - accepts any sequence
  requires true
  // All returned indices must be valid positions in the input sequence
  ensures forall i :: 0 <= i < |indices| ==> indices[i] < |a|
  // All returned indices correspond to non-zero elements in the input
  ensures forall i :: 0 <= i < |indices| ==> a[indices[i]] != 0.0
  // All non-zero elements in the input have their indices in the result
  ensures forall j :: 0 <= j < |a| && a[j] != 0.0 ==> j in indices
  // The result contains no duplicate indices
  ensures forall i, j :: 0 <= i < j < |indices| ==> indices[i] != indices[j]
  // The indices are in ascending order (ordered by their position in original vector)
  ensures forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]
// </vc-spec>
// <vc-code>
{
  indices := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < |indices| ==> indices[k] < |a|
    invariant forall k :: 0 <= k < |indices| ==> a[indices[k]] != 0.0
    invariant forall j :: 0 <= j < i && a[j] != 0.0 ==> j in indices
    invariant forall k, l :: 0 <= k < l < |indices| ==> indices[k] != indices[l]
    invariant forall k, l :: 0 <= k < l < |indices| ==> indices[k] < indices[l]
    invariant forall k :: 0 <= k < |indices| ==> indices[k] < i
  {
    if a[i] != 0.0 {
      indices := indices + [i];
    }
    i := i + 1;
  }
}
// </vc-code>
