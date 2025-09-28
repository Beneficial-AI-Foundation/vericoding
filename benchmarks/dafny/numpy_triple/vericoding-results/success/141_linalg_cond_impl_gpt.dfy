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
/* helper modified by LLM (iteration 4): Prove inverse is well-formed from well-formed, square, and invertible matrix using direct equality and quantifier introduction */
lemma InverseWellFormed(m: Matrix)
  requires IsWellFormed(m)
  requires IsSquareMatrix(m) && IsInvertible(m)
  ensures IsWellFormed(MatrixInverse(m))
{
  assert |m| > 0;
  assert |MatrixInverse(m)| == |m|;
  assert |MatrixInverse(m)| > 0;
  forall i | 0 <= i && i < |MatrixInverse(m)|
    ensures |MatrixInverse(m)[i]| == |MatrixInverse(m)[0]|
  {
    assert |MatrixInverse(m)| == |m|;
    assert 0 <= i && i < |m|;
    assert |m[i]| == |m[0]|;
    assert MatrixInverse(m) == m;
    assert |MatrixInverse(m)[i]| == |m[i]|;
    assert |MatrixInverse(m)[0]| == |m[0]|;
  }
}

/* helper modified by LLM (iteration 4): Establish that the condition number (product of norms) is at least 1.0 */
lemma ConditionNumberLowerBound(m: Matrix)
  requires IsWellFormed(m)
  requires IsSquareMatrix(m)
  requires IsInvertible(m)
  ensures MatrixNorm(m) * MatrixNorm(MatrixInverse(m)) >= 1.0
{
  InverseWellFormed(m);
  assert MatrixNorm(m) == 1.0;
  assert MatrixNorm(MatrixInverse(m)) == 1.0;
  assert MatrixNorm(m) * MatrixNorm(MatrixInverse(m)) == 1.0;
  assert MatrixNorm(m) * MatrixNorm(MatrixInverse(m)) >= 1.0;
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
  /* code modified by LLM (iteration 4): compute condition number from norms and appeal to helper for well-formed inverse and lower bound */
  InverseWellFormed(x);
  result := MatrixNorm(x) * MatrixNorm(MatrixInverse(x));
  ConditionNumberLowerBound(x);
}
// </vc-code>
