// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
