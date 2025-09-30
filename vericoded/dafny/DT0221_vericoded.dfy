// <vc-preamble>
// Define matrix as sequence of sequences of real numbers
type Matrix = seq<seq<real>>

// Predicate to check if matrix is square
predicate IsSquareMatrix(m: Matrix)
{
    |m| > 0 && forall i :: 0 <= i < |m| ==> |m[i]| == |m|
}

// Predicate to check if matrix has consistent row dimensions
predicate IsWellFormed(m: Matrix)
{
    |m| > 0 && forall i :: 0 <= i < |m| ==> |m[i]| == |m[0]|
}

// Ghost predicate representing matrix invertibility (non-zero determinant)
predicate IsInvertible(m: Matrix)
    requires IsSquareMatrix(m)
{
    true
}

// Ghost function representing the 2-norm of a matrix
function MatrixNorm(m: Matrix): real
    requires IsWellFormed(m)
    ensures MatrixNorm(m) >= 0.0
{
    1.0
}

// Ghost function representing matrix inverse
function MatrixInverse(m: Matrix): Matrix
    requires IsSquareMatrix(m) && IsInvertible(m)
    ensures IsSquareMatrix(MatrixInverse(m))
    ensures |MatrixInverse(m)| == |m|
{
    m
}

// Method to compute the condition number of a matrix
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ConditionNumber(x: Matrix) returns (result: real)
    // Matrix must be square, well-formed, and invertible
    requires IsWellFormed(x)
    requires IsSquareMatrix(x)
    requires IsInvertible(x)
    // Condition number is non-negative and at least 1 for any invertible matrix
    ensures result >= 0.0
    ensures result >= 1.0
    // The condition number equals ||A|| * ||A^(-1)||
    ensures result == MatrixNorm(x) * MatrixNorm(MatrixInverse(x))
// </vc-spec>
// <vc-code>
{
  var norm_x := MatrixNorm(x);
  var inv_x := MatrixInverse(x);
  var norm_inv_x := MatrixNorm(inv_x);
  result := norm_x * norm_inv_x;
}
// </vc-code>
