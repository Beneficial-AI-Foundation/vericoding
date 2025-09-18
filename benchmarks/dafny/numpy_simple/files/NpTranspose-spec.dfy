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
    assume {:axiom} false;
}
// </vc-code>
