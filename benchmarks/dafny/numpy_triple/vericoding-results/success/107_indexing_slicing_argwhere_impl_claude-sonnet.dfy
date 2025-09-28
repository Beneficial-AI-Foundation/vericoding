// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added lemma to establish relationship between index positions and values */
lemma IndicesPreservation(indices: seq<int>, newIndex: int, i: int)
  requires forall k :: 0 <= k < |indices| ==> 0 <= indices[k] < i
  requires 0 <= newIndex == i
  ensures forall k :: 0 <= k < |indices + [newIndex]| ==> 0 <= (indices + [newIndex])[k] <= i
{
  var newIndices := indices + [newIndex];
  forall k | 0 <= k < |newIndices|
    ensures 0 <= newIndices[k] <= i
  {
    if k < |indices| {
      assert newIndices[k] == indices[k];
      assert 0 <= indices[k] < i;
    } else {
      assert k == |indices|;
      assert newIndices[k] == newIndex == i;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method argwhere(a: seq<real>) returns (indices: seq<int>)
  // All returned indices are valid and correspond to non-zero elements
  ensures forall i :: 0 <= i < |indices| ==> 
            0 <= indices[i] < |a| && a[indices[i]] != 0.0
  
  // Completeness: all non-zero elements in input have their indices in result
  ensures forall j :: 0 <= j < |a| && a[j] != 0.0 ==> 
            j in indices
  
  // No duplicate indices in the result
  ensures forall i, j :: 0 <= i < j < |indices| ==> 
            indices[i] != indices[j]
  
  // Indices are ordered according to their position in the original array
  ensures forall i, j :: 0 <= i < j < |indices| ==> 
            indices[i] < indices[j]
  
  // Result is empty if and only if all elements in input are zero
  ensures (|indices| == 0) <==> 
          (forall k :: 0 <= k < |a| ==> a[k] == 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): simplified invariants to avoid quantifier trigger issues */
  indices := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < |indices| ==> 0 <= indices[k] < |a| && a[indices[k]] != 0.0
    invariant forall j :: 0 <= j < i && a[j] != 0.0 ==> j in indices
    invariant forall k :: 0 <= k < |indices| ==> indices[k] < i
    invariant forall k, l :: 0 <= k < l < |indices| ==> indices[k] < indices[l]
    invariant (|indices| == 0) ==> (forall k :: 0 <= k < i ==> a[k] == 0.0)
    invariant (forall k :: 0 <= k < i ==> a[k] == 0.0) ==> (|indices| == 0)
  {
    if a[i] != 0.0 {
      indices := indices + [i];
    }
    i := i + 1;
  }
}
// </vc-code>
