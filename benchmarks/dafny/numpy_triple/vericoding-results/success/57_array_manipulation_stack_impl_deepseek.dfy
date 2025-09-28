// <vc-preamble>
// Stack method that takes a sequence of vectors (each vector is a sequence of reals)
// and returns a 2D matrix where each input vector becomes a row
// </vc-preamble>

// <vc-helpers>

  // Helper function to get the length of the first array (all arrays should have this length)
  function GetRowLength(arrays: seq<seq<real>>): int
    requires |arrays| > 0
  {
    |arrays[0]|
  }

  // Helper predicate to check if all arrays have the same length
  predicate ArraysSameLength(arrays: seq<seq<real>>)
  {
    |arrays| > 0 &&
    (forall i :: 0 <= i < |arrays| ==> |arrays[i]| == |arrays[0]|)
  }

// </vc-helpers>

// <vc-spec>
method Stack(arrays: seq<seq<real>>) returns (result: seq<seq<real>>)
  // Input must be non-empty and all vectors must have the same length
  requires |arrays| > 0
  requires forall i :: 0 <= i < |arrays| ==> |arrays[i]| == |arrays[0]|
  
  // Output has the same number of rows as input vectors
  ensures |result| == |arrays|
  
  // Each row in the result has the same length as the input vectors
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |arrays[0]|
  
  // Each element in the result matrix exactly matches the corresponding element in the input
  // The i-th row of the result equals the i-th input vector
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==> 
    result[i][j] == arrays[i][j]
  
  // The stacking preserves all input vectors as rows - each row is identical to its corresponding input vector
  ensures forall i :: 0 <= i < |result| ==> result[i] == arrays[i]
// </vc-spec>
// <vc-code>
{
  var rows := |arrays|;
  var cols := |arrays[0]|;
  var matrix := [];
  
  var i := 0;
  while i < rows
    invariant 0 <= i <= rows
    invariant |matrix| == i
    invariant forall k :: 0 <= k < i ==> |matrix[k]| == cols
    invariant forall k, j :: 0 <= k < i && 0 <= j < cols ==> matrix[k][j] == arrays[k][j]
  {
    matrix := matrix + [arrays[i]];
    i := i + 1;
  }
  
  result := matrix;
}
// </vc-code>
