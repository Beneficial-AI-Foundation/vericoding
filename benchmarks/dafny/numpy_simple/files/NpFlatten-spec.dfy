// <vc-preamble>
/* Matrix type definition - 2D array represented as sequence of sequences */
datatype Matrix = Matrix(data: seq<seq<int>>, rows: nat, cols: nat)

predicate MatrixValid(mat: Matrix)
{
    |mat.data| == mat.rows &&
    (forall i :: 0 <= i < mat.rows ==> |mat.data[i]| == mat.cols)
}

function MatrixSize(mat: Matrix): nat
{
    mat.rows * mat.cols
}

function MatrixGet(mat: Matrix, i: nat, j: nat): int
    requires MatrixValid(mat)
    requires i < mat.rows && j < mat.cols
{
    mat.data[i][j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Flatten2(mat: Matrix) returns (ret: seq<int>)
    requires mat.rows > 0
    requires mat.cols > 0
    requires MatrixValid(mat)
    ensures |ret| == mat.rows * mat.cols
    ensures forall i, j :: 
        0 <= i < mat.rows && 0 <= j < mat.cols ==> 
        0 <= i * mat.cols + j < |ret| && ret[i * mat.cols + j] == MatrixGet(mat, i, j)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
