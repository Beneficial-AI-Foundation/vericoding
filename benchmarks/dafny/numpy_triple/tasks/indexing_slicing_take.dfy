// <vc-preamble>
// Take elements from a source array at specified indices
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Take(arr: seq<real>, indices: seq<int>) returns (result: seq<real>)
  // All indices must be valid positions in the source array
  requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |arr|
  // Result has the same length as the indices array
  ensures |result| == |indices|
  // Each element in result comes from the corresponding indexed position in arr
  ensures forall i :: 0 <= i < |indices| ==> result[i] == arr[indices[i]]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
