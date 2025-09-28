// <vc-preamble>
// Method that creates a triangular matrix with ones at and below the k-th diagonal
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): tri_elem returns 1.0 when j <= i + k else 0.0 */
function tri_elem(i: int, j: int, k: int): real {
  if j <= i + k then 1.0 else 0.0
}
// </vc-helpers>

// <vc-spec>
method tri(N: nat, M: nat, k: int) returns (result: seq<seq<real>>)
  // The result has exactly N rows
  ensures |result| == N
  // Each row has exactly M columns
  ensures forall i :: 0 <= i < N ==> |result[i]| == M
  // Each element is 1.0 if column index <= row index + k, otherwise 0.0
  ensures forall i, j :: 0 <= i < N && 0 <= j < M ==> 
    result[i][j] == (if j <= i + k then 1.0 else 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): build N x M sequence with strengthened invariants */
  var rows: seq<seq<real>> := [];
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant |rows| == i
    invariant forall ii :: 0 <= ii < i ==> |rows[ii]| == M
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < M ==> rows[ii][jj] == (if jj <= ii + k then 1.0 else 0.0)
  {
    var row: seq<real> := [];
    var j := 0;
    while j < M
      invariant 0 <= j <= M
      invariant |row| == j
      invariant forall jj :: 0 <= jj < j ==> row[jj] == (if jj <= i + k then 1.0 else 0.0)
    {
      row := row + [tri_elem(i, j, k)];
      j := j + 1;
    }
    rows := rows + [row];
    i := i + 1;
  }
  result := rows;
}
// </vc-code>
