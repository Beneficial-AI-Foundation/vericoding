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
/* helper modified by LLM (iteration 5): Fixed lemma assertions and added proper witness construction */
lemma WitnessElementsProperty(op: BinaryOp, arr: seq<real>, i: nat, indices: seq<nat>, result: seq<real>)
    requires ValidIndices(indices, |arr|)
    requires 0 <= i < |indices|
    requires |result| > i
    requires i < |indices| - 1 ==> (
        var startIdx := indices[i];
        var endIdx := indices[i + 1];
        if startIdx < endIdx then
            var slice := ExtractSlice(arr, startIdx, endIdx);
            |slice| > 0 && result[i] == LeftFold(op, slice)
        else
            result[i] == arr[startIdx]
    )
    requires i == |indices| - 1 ==> (
        var startIdx := indices[i];
        var slice := ExtractSlice(arr, startIdx, |arr|);
        |slice| > 0 && result[i] == LeftFold(op, slice)
    )
    ensures exists elements: seq<real> :: 
        |elements| > 0 && 
        (forall j :: 0 <= j < |elements| ==> exists k :: 0 <= k < |arr| && elements[j] == arr[k]) &&
        result[i] == LeftFold(op, elements)
{
    if i < |indices| - 1 {
        var startIdx := indices[i];
        var endIdx := indices[i + 1];
        if startIdx < endIdx {
            var slice := ExtractSlice(arr, startIdx, endIdx);
            forall j | 0 <= j < |slice|
                ensures exists k :: 0 <= k < |arr| && slice[j] == arr[k]
            {
                assert slice[j] == arr[startIdx + j];
                assert 0 <= startIdx + j < |arr|;
            }
        } else {
            var elements := [arr[startIdx]];
            assert |elements| > 0;
            assert elements[0] == arr[startIdx];
            assert startIdx < |arr|;
        }
    } else {
        var startIdx := indices[i];
        var slice := ExtractSlice(arr, startIdx, |arr|);
        forall j | 0 <= j < |slice|
            ensures exists k :: 0 <= k < |arr| && slice[j] == arr[k]
        {
            assert slice[j] == arr[startIdx + j];
            assert 0 <= startIdx + j < |arr|;
        }
    }
}

/* helper modified by LLM (iteration 5): Fixed lemma with proper quantifier structure */
lemma SliceProperty(arr: seq<real>, start: nat, end: nat)
    requires 0 <= start <= end <= |arr|
    ensures forall j :: 0 <= j < end - start ==> exists k :: 0 <= k < |arr| && arr[start..end][j] == arr[k]
{
    forall j | 0 <= j < end - start
        ensures exists k :: 0 <= k < |arr| && arr[start..end][j] == arr[k]
    {
        assert arr[start..end][j] == arr[start + j];
        assert 0 <= start + j < |arr|;
    }
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
  /* code modified by LLM (iteration 5): Fixed witness construction and postcondition proof */
  result := [];
  for i := 0 to |indices|
    invariant 0 <= i <= |indices|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> 
        (j < |indices| - 1 ==> (
            var startIdx := indices[j];
            var endIdx := indices[j + 1];
            if startIdx < endIdx then
                var slice := ExtractSlice(arr, startIdx, endIdx);
                |slice| > 0 && result[j] == LeftFold(op, slice)
            else
                result[j] == arr[startIdx]
        )) &&
        (j == |indices| - 1 ==> (
            var startIdx := indices[j];
            var slice := ExtractSlice(arr, startIdx, |arr|);
            |slice| > 0 && result[j] == LeftFold(op, slice)
        ))
    invariant forall j :: 0 <= j < i ==> 
        exists elements: seq<real> :: 
            |elements| > 0 && 
            (forall k :: 0 <= k < |elements| ==> exists l :: 0 <= l < |arr| && elements[k] == arr[l]) &&
            result[j] == LeftFold(op, elements)
  {
    var startIdx := indices[i];
    
    if i < |indices| - 1 {
      var endIdx := indices[i + 1];
      if startIdx < endIdx {
        var slice := ExtractSlice(arr, startIdx, endIdx);
        assert slice == arr[startIdx..endIdx];
        forall j | 0 <= j < |slice|
          ensures exists k :: 0 <= k < |arr| && slice[j] == arr[k]
        {
          assert slice[j] == arr[startIdx + j];
          assert 0 <= startIdx + j < |arr|;
        }
        result := result + [LeftFold(op, slice)];
      } else {
        var singleElement := [arr[startIdx]];
        assert singleElement[0] == arr[startIdx];
        assert startIdx < |arr|;
        result := result + [arr[startIdx]];
      }
    } else {
      var slice := ExtractSlice(arr, startIdx, |arr|);
      assert slice == arr[startIdx..|arr|];
      forall j | 0 <= j < |slice|
        ensures exists k :: 0 <= k < |arr| && slice[j] == arr[k]
      {
        assert slice[j] == arr[startIdx + j];
        assert 0 <= startIdx + j < |arr|;
      }
      result := result + [LeftFold(op, slice)];
    }
    
    WitnessElementsProperty(op, arr, i, indices, result);
  }
}
// </vc-code>
