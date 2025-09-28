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
/* helper modified by LLM (iteration 5): Added explicit slice property return and fixed element existence proof */
lemma ExtractSliceElements(arr: seq<real>, start: nat, end: nat) returns (slice: seq<real>)
    requires 0 <= start <= end <= |arr|
    ensures slice == ExtractSlice(arr, start, end)
    ensures forall j :: 0 <= j < |slice| ==> exists k :: 0 <= k < |arr| && slice[j] == arr[k]
{
    slice := ExtractSlice(arr, start, end);
    assert slice == arr[start..end];
    forall j | 0 <= j < |slice|
        ensures exists k :: 0 <= k < |arr| && slice[j] == arr[k]
    {
        var k := start + j;
        assert 0 <= k < |arr|;
        assert slice[j] == arr[k];
    }
}

lemma SingleElementFold(op: BinaryOp, arr: seq<real>, idx: nat)
    requires 0 <= idx < |arr|
    ensures exists elements: seq<real> :: 
        |elements| > 0 && 
        (forall j :: 0 <= j < |elements| ==> exists k :: 0 <= k < |arr| && elements[j] == arr[k]) &&
        arr[idx] == LeftFold(op, elements)
{
    var elements := [arr[idx]];
    assert |elements| == 1;
    assert elements[0] == arr[idx];
    
    // Prove element existence
    assert forall j :: 0 <= j < |elements| ==> exists k :: 0 <= k < |arr| && elements[j] == arr[k] by {
        forall j | 0 <= j < |elements|
            ensures exists k :: 0 <= k < |arr| && elements[j] == arr[k]
        {
            assert j == 0;
            assert elements[j] == arr[idx];
            assert 0 <= idx < |arr| && elements[j] == arr[idx];
        }
    }
    
    // Prove LeftFold equality
    reveal LeftFold();
    assert |elements| == 1;
    assert LeftFold(op, elements) == elements[0];
    assert elements[0] == arr[idx];
    assert arr[idx] == LeftFold(op, elements);
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
/* code modified by LLM (iteration 5): Fixed witness element tracking and invariant maintenance */
{
    result := [];
    var i := 0;
    
    while i < |indices|
        invariant 0 <= i <= |indices|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> 
            // For non-last indices
            (j < |indices| - 1 ==> (
                var startIdx := indices[j];
                var endIdx := indices[j + 1];
                if startIdx < endIdx then
                    var slice := ExtractSlice(arr, startIdx, endIdx);
                    |slice| > 0 && result[j] == LeftFold(op, slice)
                else
                    result[j] == arr[startIdx]
            )) &&
            // For the last index
            (j == |indices| - 1 ==> (
                var startIdx := indices[j];
                var slice := ExtractSlice(arr, startIdx, |arr|);
                |slice| > 0 && result[j] == LeftFold(op, slice)
            ))
        invariant forall j :: 0 <= j < i ==> 
            exists elements: seq<real> :: 
                |elements| > 0 && 
                (forall k :: 0 <= k < |elements| ==> exists m :: 0 <= m < |arr| && elements[k] == arr[m]) &&
                result[j] == LeftFold(op, elements)
    {
        var startIdx := indices[i];
        
        if i < |indices| - 1 {
            // Not the last index
            var endIdx := indices[i + 1];
            
            if startIdx < endIdx {
                // Normal forward slice
                var slice := ExtractSlice(arr, startIdx, endIdx);
                assert |slice| > 0;
                var reducedValue := LeftFold(op, slice);
                result := result + [reducedValue];
                
                // Establish element existence for this result
                var witness_slice := ExtractSliceElements(arr, startIdx, endIdx);
                assert witness_slice == slice;
                assert |witness_slice| > 0;
                assert forall k :: 0 <= k < |witness_slice| ==> exists m :: 0 <= m < |arr| && witness_slice[k] == arr[m];
                assert reducedValue == LeftFold(op, witness_slice);
                assert exists elements: seq<real> :: 
                    |elements| > 0 && 
                    (forall k :: 0 <= k < |elements| ==> exists m :: 0 <= m < |arr| && elements[k] == arr[m]) &&
                    reducedValue == LeftFold(op, elements);
            } else {
                // Backward or equal indices
                result := result + [arr[startIdx]];
                
                // Establish element existence for single element
                SingleElementFold(op, arr, startIdx);
                assert exists elements: seq<real> :: 
                    |elements| > 0 && 
                    (forall k :: 0 <= k < |elements| ==> exists m :: 0 <= m < |arr| && elements[k] == arr[m]) &&
                    arr[startIdx] == LeftFold(op, elements);
            }
        } else {
            // Last index - reduce from here to end of array
            var slice := ExtractSlice(arr, startIdx, |arr|);
            assert |slice| > 0;
            var reducedValue := LeftFold(op, slice);
            result := result + [reducedValue];
            
            // Establish element existence for this result
            var witness_slice := ExtractSliceElements(arr, startIdx, |arr|);
            assert witness_slice == slice;
            assert |witness_slice| > 0;
            assert forall k :: 0 <= k < |witness_slice| ==> exists m :: 0 <= m < |arr| && witness_slice[k] == arr[m];
            assert reducedValue == LeftFold(op, witness_slice);
            assert exists elements: seq<real> :: 
                |elements| > 0 && 
                (forall k :: 0 <= k < |elements| ==> exists m :: 0 <= m < |arr| && elements[k] == arr[m]) &&
                reducedValue == LeftFold(op, elements);
        }
        
        i := i + 1;
    }
}
// </vc-code>
