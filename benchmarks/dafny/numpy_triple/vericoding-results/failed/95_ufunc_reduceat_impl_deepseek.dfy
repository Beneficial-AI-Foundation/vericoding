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
function ReduceSegment(op: BinaryOp, arr: seq<real>, start: nat, end: nat): real
    requires 0 <= start <= end <= |arr|
    requires start < end
    decreases end - start
{
    if start + 1 == end then
        arr[start]
    else
        op(arr[start], ReduceSegment(op, arr, start + 1, end))
}

/* helper modified by LLM (iteration 5): Fixed lemma proofs with proper unfolding */
lemma LeftFoldEqualsReduceSegment(op: BinaryOp, arr: seq<real>, start: nat, end: nat)
    requires 0 <= start <= end <= |arr|
    requires start < end
    ensures LeftFold(op, ExtractSlice(arr, start, end)) == ReduceSegment(op, arr, start, end)
    decreases end - start
{
    if start + 1 == end {
        // Base case: single element slice
        unfold LeftFold;
        assert ExtractSlice(arr, start, end) == [arr[start]];
    } else {
        LeftFoldEqualsReduceSegment(op, arr, start + 1, end);
        unfold LeftFold;
        var recursiveSlice := ExtractSlice(arr, start + 1, end);
        assert LeftFold(op, ExtractSlice(arr, start + 1, end)) == ReduceSegment(op, arr, start + 1, end);
    }
}

/* helper modified by LLM (iteration 5): Fixed lemma to use the main lemma */
lemma LeftFoldEqualsReduceSegmentLast(op: BinaryOp, arr: seq<real>, start: nat)
    requires 0 <= start < |arr|
    ensures LeftFold(op, ExtractSlice(arr, start, |arr|)) == ReduceSegment(op, arr, start, |arr|)
{
    LeftFoldEqualsReduceSegment(op, arr, start, |arr|);
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
  /* code modified by LLM (iteration 5): Fixed implementation with proper loop invariants */
  result := [];
  var i := 0;
  while i < |indices|
    invariant |result| == i
    invariant i <= |indices|
    invariant forall j :: 0 <= j < i ==>
        if j < |indices| - 1 then
            var startIdx := indices[j];
            var endIdx := indices[j + 1];
            if startIdx < endIdx then
                result[j] == LeftFold(op, ExtractSlice(arr, startIdx, endIdx))
            else
                result[j] == arr[startIdx]
        else
            result[j] == LeftFold(op, ExtractSlice(arr, indices[j], |arr|))
  {
    if i < |indices| - 1 {
        var startIdx := indices[i];
        var endIdx := indices[i + 1];
        if startIdx < endIdx {
            LeftFoldEqualsReduceSegment(op, arr, startIdx, endIdx);
            result := result + [LeftFold(op, ExtractSlice(arr, startIdx, endIdx))];
        } else {
            result := result + [arr[startIdx]];
        }
    } else {
        var startIdx := indices[i];
        LeftFoldEqualsReduceSegmentLast(op, arr, startIdx);
        result := result + [LeftFold(op, ExtractSlice(arr, startIdx, |arr|))];
    }
    i := i + 1;
  }
}
// </vc-code>
