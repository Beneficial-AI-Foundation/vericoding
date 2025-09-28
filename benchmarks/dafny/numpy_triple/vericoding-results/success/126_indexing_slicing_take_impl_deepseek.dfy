// <vc-preamble>
// Take elements from a source array at specified indices
// </vc-preamble>

// <vc-helpers>

  // Helper predicate to check if all indices are valid
  predicate ValidIndices(arr: seq<real>, indices: seq<int>)
  {
    forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |arr|
  }

  // Helper lemma to access array elements through valid indices
  lemma ArrayAccessLemma(arr: seq<real>, indices: seq<int>, i: int)
    requires ValidIndices(arr, indices)
    requires 0 <= i < |indices|
    ensures 0 <= indices[i] < |arr|
  {
  }

  // Helper lemma to prove result length invariant
  lemma ResultLengthLemma(result: seq<real>, idx: int, indices: seq<int>)
    requires |result| == idx
    requires idx <= |indices|
    ensures |result| == idx
  {
  }

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
  /* code modified by LLM (iteration 3): Fixed postcondition verification by ensuring proper array bounds */
  result := [];
  var idx := 0;
  
  while idx < |indices|
    invariant |result| == idx
    invariant idx <= |indices|
    invariant forall j :: 0 <= j < idx ==> result[j] == arr[indices[j]]
  {
    ArrayAccessLemma(arr, indices, idx);
    result := result + [arr[indices[idx]]];
    ResultLengthLemma(result, idx + 1, indices);
    idx := idx + 1;
  }
}
// </vc-code>
