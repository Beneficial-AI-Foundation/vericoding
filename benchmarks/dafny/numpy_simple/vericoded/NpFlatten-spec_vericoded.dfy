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
function FlattenHelper(mat: Matrix, row: nat): seq<int>
    requires MatrixValid(mat)
    requires row <= mat.rows
    decreases mat.rows - row
{
    if row == mat.rows then []
    else mat.data[row] + FlattenHelper(mat, row + 1)
}

lemma FlattenHelperLength(mat: Matrix, row: nat)
    requires MatrixValid(mat)
    requires row <= mat.rows
    ensures |FlattenHelper(mat, row)| == (mat.rows - row) * mat.cols
    decreases mat.rows - row
{
    if row == mat.rows {
    } else {
        FlattenHelperLength(mat, row + 1);
    }
}

lemma FlattenHelperCorrect(mat: Matrix, row: nat, i: nat, j: nat)
    requires MatrixValid(mat)
    requires row <= mat.rows
    requires row <= i < mat.rows
    requires 0 <= j < mat.cols
    ensures 0 <= (i - row) * mat.cols + j < |FlattenHelper(mat, row)|
    ensures FlattenHelper(mat, row)[(i - row) * mat.cols + j] == MatrixGet(mat, i, j)
    decreases mat.rows - row
{
    FlattenHelperLength(mat, row);
    if row == i {
        assert FlattenHelper(mat, row)[(i - row) * mat.cols + j] == mat.data[row][j];
    } else {
        FlattenHelperCorrect(mat, row + 1, i, j);
        assert FlattenHelper(mat, row)[(i - row) * mat.cols + j] == FlattenHelper(mat, row + 1)[(i - row - 1) * mat.cols + j];
    }
}
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
    ret := FlattenHelper(mat, 0);
    FlattenHelperLength(mat, 0);
    assert |ret| == mat.rows * mat.cols;
    
    forall i, j | 0 <= i < mat.rows && 0 <= j < mat.cols
        ensures 0 <= i * mat.cols + j < |ret|
        ensures ret[i * mat.cols + j] == MatrixGet(mat, i, j)
    {
        FlattenHelperCorrect(mat, 0, i, j);
    }
}
// </vc-code>
