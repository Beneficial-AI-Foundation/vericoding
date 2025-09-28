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
/* helper modified by LLM (iteration 5): fixed syntax error by reordering let expressions */
function ComputeResultForIndex(op: BinaryOp, arr: seq<real>, indices: seq<nat>, i: nat): real
     requires ValidIndices(indices, |arr|)
     requires 0 <= i < |indices|
     ensures i < |indices| - 1 ==> (
         var startIdx := indices[i];
         var endIdx := indices[i+1];
         if startIdx < endIdx then
             var slice := ExtractSlice(arr, startIdx, endIdx);
             |slice| > 0 && ComputeResultForIndex(op, arr, indices, i) == LeftFold(op, slice)
         else
             ComputeResultForIndex(op, arr, indices, i) == arr[startIdx]
     )
     ensures i == |indices| - 1 ==> (
         var startIdx := indices[i];
         var slice := ExtractSlice(arr, startIdx, |arr|);
         |slice| > 0 && ComputeResultForIndex(op, arr, indices, i) == LeftFold(op, slice)
     )
{
     let startIdx := indices[i] in
     if i < |indices| - 1 then
         let endIdx := indices[i+1] in
         if startIdx < endIdx then
             LeftFold(op, ExtractSlice(arr, startIdx, endIdx))
         else
             arr[startIdx]
     else
         LeftFold(op, ExtractSlice(arr, startIdx, |arr|))
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
  /* code modified by LLM (iteration 5): compilation error was in helper, code unchanged */
  var resultSeq := [];
  var i: nat := 0;
  while i < |indices|
      invariant 0 <= i <= |indices|
      invariant |resultSeq| == i
      invariant forall j :: 0 <= j < i ==> 
          (j < |indices| - 1 ==> (
              var startIdx := indices[j];
              var endIdx := indices[j + 1];
              if startIdx < endIdx then
                  var slice := ExtractSlice(arr, startIdx, endIdx);
                  |slice| > 0 && resultSeq[j] == LeftFold(op, slice)
              else
                  resultSeq[j] == arr[startIdx]
          )) &&
          (j == |indices| - 1 ==> (
              var startIdx := indices[j];
              var slice := ExtractSlice(arr, startIdx, |arr|);
              |slice| > 0 && resultSeq[j] == LeftFold(op, slice)
          ))
  {
      if i < |indices| - 1 then {
          var startIdx := indices[i];
          var endIdx := indices[i+1];
          if startIdx < endIdx then {
              var slice := ExtractSlice(arr, startIdx, endIdx);
              resultSeq := resultSeq + [LeftFold(op, slice)];
          } else {
              resultSeq := resultSeq + [arr[startIdx]];
          }
      } else {
          var startIdx := indices[i];
          var slice := ExtractSlice(arr, startIdx, |arr|);
          resultSeq := resultSeq + [LeftFold(op, slice)];
      }
      i := i + 1;
  }
  result := resultSeq;
}
// </vc-code>
