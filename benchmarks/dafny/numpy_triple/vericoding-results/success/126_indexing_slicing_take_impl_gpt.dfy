// <vc-preamble>
// Take elements from a source array at specified indices
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no helpers required for this implementation */
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
  /* code modified by LLM (iteration 2): implement take by iterating indices and building result */
  var r: seq<real> := [];
  var i := 0;
  while i < |indices|
    invariant 0 <= i <= |indices|
    invariant |r| == i
    invariant forall k :: 0 <= k < i ==> r[k] == arr[indices[k]]
    decreases |indices| - i
  {
    r := r + [arr[indices[i]]];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
