// <vc-preamble>
// Type alias for binary operation on reals
type BinaryOp = (real, real) -> real

// Helper predicate to check if all indices are valid for the given array length
predicate ValidIndices(indices: seq<nat>, arrayLen: nat)
{
    arrayLen > 0 && |indices| > 0 && forall i :: 0 <= i < |indices| ==> indices[i] < arrayLen
}

// Helper function to extract a slice from an array between two indices
function ExtractSlice(arr: seq<real>, start: nat, end: nat): seq<real>
    requires 0 <= start <= end <= |arr|
{
    arr[start..end]
}

// Helper function to perform left-associative fold on a non-empty sequence
function {:opaque} LeftFold(op: BinaryOp, elements: seq<real>): real
    requires |elements| > 0
{
    if |elements| == 1 then
        elements[0]
    else
        op(elements[0], LeftFold(op, elements[1..]))
}

// Main reduceat method specification
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [no changes, helper is correct] */
lemma {:vcs_split_i 2} Reveal_LeftFold(op: BinaryOp, elements: seq<real>)
    requires |elements| > 0
    ensures |elements| == 1 ==> LeftFold(op, elements) == elements[0]
    ensures |elements| > 1 ==> LeftFold(op, elements) == op(elements[0], LeftFold(op, elements[1..]))
{
    reveal LeftFold();
}
// </vc-helpers>

// <vc-spec>
method ReduceAt(op: BinaryOp, arr: seq<real>, indices: seq<nat>) returns (result: seq<real>)
    requires ValidIndices(indices, |arr|)
    ensures |result| == |indices|
    ensures forall i :: 0 <= i < |indices| ==> 
        // For non-last indices
        (i < |indices| - 1 ==> (
            var startIdx := indices[i];
            var endIdx := indices[i + 1];
            // Case 1: Normal forward slice (start < end)
            if startIdx < endIdx then
                var slice := ExtractSlice(arr, startIdx, endIdx);
                |slice| > 0 && result[i] == LeftFold(op, slice)
            // Case 2: Backward or equal indices (start >= end) 
            else
                result[i] == arr[startIdx]
        )) &&
        // For the last index: reduce from indices[i] to end of array
        (i == |indices| - 1 ==> (
            var startIdx := indices[i];
            var slice := ExtractSlice(arr, startIdx, |arr|);
            |slice| > 0 && result[i] == LeftFold(op, slice)
        ))
    ensures forall i :: 0 <= i < |indices| ==> 
        // All result elements are well-defined based on array contents
        exists elements: seq<real> :: 
            |elements| > 0 && 
            (forall j :: 0 <= j < |elements| ==> exists k :: 0 <= k < |arr| && elements[j] == arr[k]) &&
            result[i] == LeftFold(op, elements)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): [fixed invalid syntax in multi-binding let-expressions in loop invariants] */
  var res_m := new real[|indices|];
  var i: nat := 0;
  while i < |indices|
    invariant 0 <= i <= |indices|
    invariant forall k :: 0 <= k < i ==> 
        (k < |indices| - 1 ==> (
            let startIdx_k := indices[k] in let endIdx_k := indices[k + 1] in
            if startIdx_k < endIdx_k then
                let slice_k := ExtractSlice(arr, startIdx_k, endIdx_k) in
                |slice_k| > 0 && res_m[k] == LeftFold(op, slice_k)
            else
                res_m[k] == arr[startIdx_k]
        )) &&
        (k == |indices| - 1 ==> (
            let startIdx_k := indices[k] in let slice_k := ExtractSlice(arr, startIdx_k, |arr|) in
            |slice_k| > 0 && res_m[k] == LeftFold(op, slice_k)
        ))
    invariant forall k :: 0 <= k < i ==> (
        exists elements: seq<real> :: 
            |elements| > 0 && 
            (forall j :: 0 <= j < |elements| ==> exists l :: 0 <= l < |arr| && elements[j] == arr[l]) &&
            res_m[k] == LeftFold(op, elements)
    )
    decreases |indices| - i
  {
    var startIdx := indices[i];
    if i < |indices| - 1 {
      var endIdx := indices[i + 1];
      if startIdx < endIdx {
        var slice := ExtractSlice(arr, startIdx, endIdx);
        res_m[i] := LeftFold(op, slice);
      } else {
        res_m[i] := arr[startIdx];
        var single_element_seq := [arr[startIdx]];
        Reveal_LeftFold(op, single_element_seq);
        assert res_m[i] == LeftFold(op, single_element_seq);
      }
    } else {
      var slice := ExtractSlice(arr, startIdx, |arr|);
      res_m[i] := LeftFold(op, slice);
    }
    i := i + 1;
  }
  result := res_m[..];
}
// </vc-code>
