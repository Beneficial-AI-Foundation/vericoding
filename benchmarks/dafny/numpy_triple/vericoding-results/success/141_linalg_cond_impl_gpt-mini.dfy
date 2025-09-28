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
lemma InverseIsWellFormed(x: Matrix)
  requires IsSquareMatrix(x)
  requires IsInvertible(x)
  ensures IsWellFormed(MatrixInverse(x))
{
  // From the postcondition of MatrixInverse we get that it is square
  assert IsSquareMatrix(MatrixInverse(x));
  // Therefore it has positive length and all rows have the same length (equal to |MatrixInverse(x)|)
  assert |MatrixInverse(x)| > 0;
  assert forall i :: 0 <= i < |MatrixInverse(x)| ==> |MatrixInverse(x)[i]| == |MatrixInverse(x)[0]|;
}

lemma NormProductAtLeastOne(x: Matrix)
  requires IsWellFormed(x)
  requires IsSquareMatrix(x)
  requires IsInvertible(x)
  ensures MatrixNorm(x) * MatrixNorm(MatrixInverse(x)) >= 1.0
{
  // Show inverse is well formed so MatrixNorm(MatrixInverse(x)) is defined
  InverseIsWellFormed(x);
  // MatrixNorm is defined to be 1.0 for any well-formed matrix
  assert MatrixNorm(x) == 1.0;
  assert MatrixNorm(MatrixInverse(x)) == 1.0;
  assert MatrixNorm(x) * MatrixNorm(MatrixInverse(x)) == 1.0;
}
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
  var inv := MatrixInverse(x);
  // Ensure inverse is well-formed before calling MatrixNorm on it
  InverseIsWellFormed(x);
  result := MatrixNorm(x) * MatrixNorm(inv);
  // Establish the required lower bounds
  NormProductAtLeastOne(x);
  assert result == MatrixNorm(x) * MatrixNorm(inv);
  assert result >= 0.0;
  assert result >= 1.0;
}

// </vc-code>
