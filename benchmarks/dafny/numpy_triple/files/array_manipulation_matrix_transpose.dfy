// <vc-preamble>
// Type alias for better readability - represents a matrix as sequence of rows
type Matrix = seq<seq<real>>

// Predicate to check if a matrix is well-formed (all rows have same length)
predicate IsValidMatrix(mat: Matrix)
{
    |mat| > 0 && forall i :: 0 <= i < |mat| ==> |mat[i]| == |mat[0]|
}

// Helper function to get matrix dimensions
function MatrixRows(mat: Matrix): nat
    requires IsValidMatrix(mat)
{
    |mat|
}

function MatrixCols(mat: Matrix): nat
    requires IsValidMatrix(mat)
{
    |mat[0]|
}

// Method to transpose a matrix by swapping rows and columns
// For an m×n input matrix, produces an n×m output matrix where result[i][j] = input[j][i]
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MatrixTranspose(mat: Matrix) returns (result: Matrix)
    requires IsValidMatrix(mat)
    ensures IsValidMatrix(result)
    // Dimension properties: result is n×m when input is m×n
    ensures |result| == MatrixCols(mat)
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == MatrixRows(mat)
    // Core transpose property: result[i][j] = mat[j][i]
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==> 
        result[i][j] == mat[j][i]
    // Involutive property: transpose is its own inverse (mat[j][i] = result[i][j])
    ensures forall i, j :: 0 <= i < MatrixRows(mat) && 0 <= j < MatrixCols(mat) ==>
        mat[i][j] == result[j][i]
    // Bijective property: every element appears exactly once in the transpose
    ensures forall i, j :: 0 <= i < MatrixRows(mat) && 0 <= j < MatrixCols(mat) ==>
        (exists! ii, jj :: 0 <= ii < |result| && 0 <= jj < |result[ii]| && result[ii][jj] == mat[i][j] && ii == j && jj == i)
    // Matrix equality preservation: transpose preserves all matrix elements bijectively
    ensures multiset(multiset(mat[i]) | i in range(MatrixRows(mat))) == 
            multiset(multiset(result[i]) | i in range(|result|))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
