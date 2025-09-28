// <vc-preamble>
type Matrix = seq<seq<int>>

function MatrixGet(mat: Matrix, i: int, j: int): int
    requires 0 <= i < |mat|
    requires i < |mat| ==> 0 <= j < |mat[i]|
{
    mat[i][j]
}

function MatrixRows(mat: Matrix): int {
    |mat|
}

function MatrixCols(mat: Matrix): int
{
    if |mat| > 0 then |mat[0]| else 0
}

function MatrixSize(mat: Matrix): int
{
    MatrixRows(mat) * MatrixCols(mat)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma to prove bounds for rectangular matrix access */
lemma RectangularMatrixAccess(arr: Matrix, i: int, j: int)
    requires 0 <= i < |arr|
    requires forall k :: 0 <= k < |arr| ==> |arr[k]| == |arr[0]|
    requires 0 <= j < |arr[0]|
    ensures 0 <= j < |arr[i]|
{
    assert |arr[i]| == |arr[0]|;
}
// </vc-helpers>

// <vc-spec>
method Transpose(arr: Matrix) returns (ret: Matrix)
    requires |arr| > 0
    requires forall i :: 0 <= i < |arr| ==> |arr[i]| == |arr[0]|
    ensures |ret| == |arr[0]|
    ensures forall i :: 0 <= i < |ret| ==> |ret[i]| == |arr|
    ensures MatrixSize(ret) == MatrixCols(arr) * MatrixRows(arr)
    ensures forall i, j :: 
        (0 <= i < MatrixRows(arr) && 0 <= j < MatrixCols(arr)) ==>
        MatrixGet(ret, j, i) == MatrixGet(arr, i, j)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): use loops and lemma to prove bounds */
  var m := |arr|;
  var n := |arr[0]|;
  ret := [];
  for j := 0 to n
    invariant 0 <= j <= n
    invariant |ret| == j
    invariant forall k :: 0 <= k < j ==> |ret[k]| == m
    invariant forall a, b :: 0 <= a < j && 0 <= b < m ==> MatrixGet(ret, a, b) == MatrixGet(arr, b, a)
  {
    var row := [];
    for i := 0 to m
      invariant 0 <= i <= m
      invariant |row| == i
      invariant forall b :: 0 <= b < i ==> row[b] == MatrixGet(arr, b, j)
    {
      if i < m {
        RectangularMatrixAccess(arr, i, j);
        row := row + [MatrixGet(arr, i, j)];
      }
    }
    ret := ret + [row];
  }
}
// </vc-code>
