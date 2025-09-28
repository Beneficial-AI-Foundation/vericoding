// <vc-preamble>
// 3D array type: outer dimension (always 1) -> rows -> depth elements
type Array3D = seq<seq<seq<real>>>
// </vc-preamble>

// <vc-helpers>
function AllSameLength<T>(arrays: seq<seq<T>>): bool {
  if |arrays| == 0 then true else
    forall i :: 0 <= i < |arrays| ==> |arrays[i]| == |arrays[0]|
}
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
  var n := |arrays|;
  var m := |arrays[0]|;
  var grid : seq<seq<real>> := [];
  var i := 0;
  
  while i < m
    invariant 0 <= i <= m
    invariant |grid| == i
    invariant forall r :: 0 <= r < i ==> |grid[r]| == n
    invariant forall r, c :: 0 <= r < i && 0 <= c < n ==> grid[r][c] == arrays[c][r]
  {
    var row : seq<real> := [];
    var j := 0;
    
    while j < n
      invariant 0 <= j <= n
      invariant |row| == j
      invariant forall c :: 0 <= c < j ==> row[c] == arrays[c][i]
    {
      row := row + [arrays[j][i]];
      j := j + 1;
    }
    
    grid := grid + [row];
    i := i + 1;
  }
  
  result := [grid];
}
// </vc-code>
