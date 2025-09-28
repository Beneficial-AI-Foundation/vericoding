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
  /* code modified by LLM (iteration 3): Replaced sequence comprehension with imperative loops to resolve a compilation error. */
  var rows := MatrixRows(arr);
  var cols := MatrixCols(arr);

  ret := [];
  var j: int := 0;
  while j < cols
    invariant 0 <= j <= cols
    invariant |ret| == j
    invariant forall k :: 0 <= k < |ret| ==> |ret[k]| == rows
    invariant forall k, l :: (0 <= k < |ret| && 0 <= l < rows) ==> ret[k][l] == arr[l][k]
  {
    var new_row: seq<int> := [];
    var i: int := 0;
    while i < rows
      invariant 0 <= i <= rows
      invariant |new_row| == i
      invariant forall l :: 0 <= l < |new_row| ==> new_row[l] == arr[l][j]
    {
      new_row := new_row + [arr[i][j]];
      i := i + 1;
    }
    ret := ret + [new_row];
    j := j + 1;
  }
}
// </vc-code>
