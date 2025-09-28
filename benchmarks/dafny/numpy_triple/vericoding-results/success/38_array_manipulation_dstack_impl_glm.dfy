// <vc-preamble>
// 3D array type: outer dimension (always 1) -> rows -> depth elements
type Array3D = seq<seq<seq<real>>>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method numpy_dstack(arrays: seq<seq<real>>) returns (result: Array3D)
  requires |arrays| > 0
  // All input arrays must have the same length
  requires forall i, j :: 0 <= i < |arrays| && 0 <= j < |arrays| ==> |arrays[i]| == |arrays[j]|
  
  ensures |result| == 1
  // The single outer element has the same number of rows as the input array length
  ensures |arrays| > 0 ==> |result[0]| == |arrays[0]|
  // Each row has as many elements as there are input arrays (depth dimension)
  ensures |arrays| > 0 ==> forall i :: 0 <= i < |result[0]| ==> |result[0][i]| == |arrays|
  // Correct element positioning: result[0][i][j] = arrays[j][i]
  ensures |arrays| > 0 ==> forall i, j :: 
    0 <= i < |arrays[0]| && 0 <= j < |arrays| ==> 
    result[0][i][j] == arrays[j][i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): fix loop invariant to use proper quantifier scoping */
  var rows := |arrays[0]|;
  var depth := |arrays|;
  var matrix := [];
  var i := 0;
  while i < rows
    invariant 0 <= i <= rows
    invariant |matrix| == i
    // For every row k that we've built (0 <= k < i), the row has length depth and contains the correct elements.
    invariant forall k :: 0 <= k < i ==> |matrix[k]| == depth
    invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < depth ==> matrix[k][j] == arrays[j][k]
  {
    var row := [];
    var j := 0;
    while j < depth
      invariant 0 <= j <= depth
      invariant |row| == j
      // For every element l in the current row (0 <= l < j), we have row[l] == arrays[l][i]
      invariant forall l :: 0 <= l < j ==> row[l] == arrays[l][i]
    {
      row := row + [arrays[j][i]];
      j := j + 1;
    }
    // Now j == depth, so |row| = depth and for all l in [0, depth), row[l] == arrays[l][i]
    matrix := matrix + [row];
    i := i + 1;
  }
  result := [matrix];
}
// </vc-code>
