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
  if |arrays| == 0 {
    result := [];
    return;
  }
  
  var rows := |arrays[0]|;
  var depth := |arrays|;
  var resultRows: seq<seq<real>> := [];
  
  var i := 0;
  while i < rows
    invariant 0 <= i <= rows
    invariant |resultRows| == i
    invariant forall k :: 0 <= k < i ==> |resultRows[k]| == depth
    invariant forall k, j :: 0 <= k < i && 0 <= j < depth ==> resultRows[k][j] == arrays[j][k]
  {
    var row: seq<real> := [];
    var j := 0;
    while j < depth
      invariant 0 <= j <= depth
      invariant |row| == j
      invariant forall l :: 0 <= l < j ==> row[l] == arrays[l][i]
    {
      row := row + [arrays[j][i]];
      j := j + 1;
    }
    resultRows := resultRows + [row];
    i := i + 1;
  }
  
  result := [resultRows];
}
// </vc-code>
