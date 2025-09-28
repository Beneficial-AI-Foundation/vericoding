// <vc-preamble>
// 3D array type: outer dimension (always 1) -> rows -> depth elements
type Array3D = seq<seq<seq<real>>>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): predicate checking all arrays have same length */
function AllSameLength(arrays: seq<seq<real>>): bool {
  forall i, j :: 0 <= i < |arrays| && 0 <= j < |arrays| ==> |arrays[i]| == |arrays[j]|
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
  /* code modified by LLM (iteration 3): construct 3D result by stacking input arrays along depth */
  var n := |arrays|;
  var m := |arrays[0]|;
  var rows: seq<seq<real>> := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |rows| == i
    invariant forall ii :: 0 <= ii < i ==> |rows[ii]| == n
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < n ==> rows[ii][jj] == arrays[jj][ii]
  {
    var row: seq<real> := [];
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |row| == j
      invariant forall jj :: 0 <= jj < j ==> row[jj] == arrays[jj][i]
    {
      assert |arrays[j]| == m;
      row := row + [arrays[j][i]];
      j := j + 1;
    }
    rows := rows + [row];
    i := i + 1;
  }
  result := [rows];
}

// </vc-code>
