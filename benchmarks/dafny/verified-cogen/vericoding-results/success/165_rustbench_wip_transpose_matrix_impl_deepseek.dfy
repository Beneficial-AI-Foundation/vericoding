// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed assertion by using matrix dimensions lemma */
lemma MatrixDimensionsConsistent(matrix: seq<seq<int>>)
  requires |matrix| > 0
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix|
  ensures |matrix[0]| == |matrix|
{
  var n := |matrix|;
  var m := |matrix[0]|;
  assert forall i :: 0 <= i < n ==> |matrix[i]| == m;
  assert m == n;
}

// </vc-helpers>

// <vc-spec>
method Transpose(matrix: seq<seq<int>>) returns (result: seq<seq<int>>)
    requires |matrix| > 0
    requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
    requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix|
    ensures |result| == |matrix[0]|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |matrix|
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==> result[i][j] == matrix[j][i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed assertion by using proven lemma about matrix dimensions */
{
  MatrixDimensionsConsistent(matrix);
  var n := |matrix|;
  var m := |matrix[0]|;
  
  result := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == n
    invariant forall k, j :: 0 <= k < i && 0 <= j < n ==> result[k][j] == matrix[j][k]
  {
    var row := [];
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |row| == j
      invariant forall k :: 0 <= k < j ==> row[k] == matrix[k][i]
    {
      row := row + [matrix[j][i]];
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }
  
  assert |result| == m;
  assert forall k :: 0 <= k < |result| ==> |result[k]| == n;
}
// </vc-code>
