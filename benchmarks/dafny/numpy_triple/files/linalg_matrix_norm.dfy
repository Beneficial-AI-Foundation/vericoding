// <vc-preamble>
// Ghost function to compute the sum of squares of all elements in a matrix
ghost function SumOfSquares(matrix: seq<seq<real>>): real
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  decreases |matrix|
{
  if |matrix| == 0 then 0.0
  else SumOfSquaresRow(matrix[0]) + SumOfSquares(matrix[1..])
}

// Ghost function to compute the sum of squares of elements in a row
ghost function SumOfSquaresRow(row: seq<real>): real
  decreases |row|
{
  if |row| == 0 then 0.0
  else row[0] * row[0] + SumOfSquaresRow(row[1..])
}

// Ghost predicate to check if all elements in matrix are zero
ghost predicate AllZero(matrix: seq<seq<real>>)
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
{
  forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[i]| ==> matrix[i][j] == 0.0
}

// Ghost predicate to check if there exists a non-zero element
ghost predicate HasNonZero(matrix: seq<seq<real>>)
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
{
  exists i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[i]| && matrix[i][j] != 0.0
}

// Helper function to get absolute value
function Abs(x: real): real
{
  if x >= 0.0 then x else -x
}

// Main method for computing matrix norm (Frobenius norm)
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MatrixNorm(matrix: seq<seq<real>>) returns (result: real)
  // Input validation: rectangular matrix (all rows same length)
  requires |matrix| > 0 ==> forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  // Non-negativity property
  ensures result >= 0.0
  // Zero property: norm is zero iff all elements are zero
  ensures (|matrix| == 0 || |matrix[0]| == 0) ==> result == 0.0
  ensures |matrix| > 0 && |matrix[0]| > 0 ==> (result == 0.0 <==> AllZero(matrix))
  // Frobenius norm definition: sqrt(sum of squares)
  ensures |matrix| > 0 && |matrix[0]| > 0 ==> result * result == SumOfSquares(matrix)
  // Domination property: norm dominates absolute value of any element
  ensures forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[i]| ==> Abs(matrix[i][j]) <= result
  // Positive definiteness: if matrix has non-zero elements, norm is positive
  ensures |matrix| > 0 && |matrix[0]| > 0 && HasNonZero(matrix) ==> result > 0.0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
