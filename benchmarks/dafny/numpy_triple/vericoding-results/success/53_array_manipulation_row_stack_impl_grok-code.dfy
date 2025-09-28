// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RowStack(arrays: seq<seq<real>>) returns (result: seq<seq<real>>)
  // All input vectors must have the same length
  requires |arrays| > 0
  requires forall i :: 0 <= i < |arrays| ==> |arrays[i]| == |arrays[0]|
  
  // Result has same number of rows as input arrays
  ensures |result| == |arrays|
  
  // Each row in result has same length as input vectors
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |arrays[0]|
  
  // Each element is preserved: result[i][j] == arrays[i][j]
  ensures forall i, j :: 0 <= i < |arrays| && 0 <= j < |arrays[i]| ==> 
    result[i][j] == arrays[i][j]
// </vc-spec>
// <vc-code>
{
  result := arrays;
}
// </vc-code>
