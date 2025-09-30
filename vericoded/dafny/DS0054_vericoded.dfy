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
/* helper modified by LLM (iteration 2): Added helper predicate to validate matrix dimensions */
predicate ValidMatrix(mat: Matrix)
{
    |mat| > 0 && forall i :: 0 <= i < |mat| ==> |mat[i]| == |mat[0]|
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
    /* code modified by LLM (iteration 2): Added bounds checking with conditional access */
    var rows := |arr|;
    var cols := |arr[0]|;
    ret := seq(cols, i requires 0 <= i < cols => seq(rows, j requires 0 <= j < rows => if 0 <= j < |arr| && 0 <= i < |arr[j]| then arr[j][i] else 0));
}
// </vc-code>
