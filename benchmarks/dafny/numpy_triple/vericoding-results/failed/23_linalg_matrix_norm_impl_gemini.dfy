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
lemma SqrtExists(x: real)
  requires x >= 0.0
  ensures exists y: real :: y >= 0.0 && y * y == x
{ }

lemma SqrtMonotonic(a: real, b: real)
  requires a >= 0.0 && b >= 0.0
  requires a * a >= b * b
  ensures a >= b
{ }

lemma SumOfSquaresRowNonNegative(row: seq<real>)
  ensures SumOfSquaresRow(row) >= 0.0
  decreases |row|
{
  if |row| > 0 {
    SumOfSquaresRowNonNegative(row[1..]);
  }
}

lemma SumOfSquaresNonNegative(matrix: seq<seq<real>>)
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  ensures SumOfSquares(matrix) >= 0.0
  decreases |matrix|
{
  if |matrix| > 0 {
    SumOfSquaresRowNonNegative(matrix[0]);
    SumOfSquaresNonNegative(matrix[1..]);
  }
}

lemma SumOfSquaresRowBoundsElement(row: seq<real>, c: int)
  requires 0 <= c < |row|
  ensures SumOfSquaresRow(row) >= row[c] * row[c]
  decreases |row|
{
  if c == 0 {
    if |row| > 1 {
      SumOfSquaresRowNonNegative(row[1..]);
    }
  } else {
    SumOfSquaresRowBoundsElement(row[1..], c - 1);
  }
}

lemma SumOfSquaresBoundsElement(matrix: seq<seq<real>>, r: int, c: int)
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  requires 0 <= r < |matrix|
  requires 0 <= c < |matrix[r]|
  ensures SumOfSquares(matrix) >= matrix[r][c] * matrix[r][c]
  decreases |matrix|
{
  if r == 0 {
    if |matrix| > 1 {
      SumOfSquaresNonNegative(matrix[1..]);
    }
    SumOfSquaresRowBoundsElement(matrix[0], c);
  } else {
    SumOfSquaresBoundsElement(matrix[1..], r - 1, c);
    SumOfSquaresRowNonNegative(matrix[0]);
  }
}
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
  if |matrix| == 0 || (|matrix| > 0 && |matrix[0]| == 0) {
    result := 0.0;
  } else {
    var sum_sq: real := 0.0;
    var i := 0;
    while i < |matrix|
      invariant 0 <= i <= |matrix|
      invariant sum_sq == SumOfSquares(matrix[..i])
      invariant forall r :: 0 <= r < i ==> |matrix[r]| == |matrix[0]|
    {
      var row_sum_sq: real := 0.0;
      var j := 0;
      var currentRow := matrix[i];
      while j < |currentRow|
        invariant 0 <= j <= |currentRow|
        invariant row_sum_sq == SumOfSquaresRow(currentRow[..j])
      {
        var val := currentRow[j];
        row_sum_sq := row_sum_sq + val * val;
        j := j + 1;
      }
      sum_sq := sum_sq + row_sum_sq;
      i := i + 1;
    }
    
    assert sum_sq >= 0.0;
    SqrtExists(sum_sq);
    var r :| r >= 0.0 && r * r == sum_sq;
    result := r;

    forall i, j | 0 <= i < |matrix| && 0 <= j < |matrix[i]|
      ensures Abs(matrix[i][j]) <= result
    {
      SumOfSquaresBoundsElement(matrix, i, j);
      assert result * result == sum_sq >= matrix[i][j] * matrix[i][j];
      assert result * result >= Abs(matrix[i][j]) * Abs(matrix[i][j]);
      SqrtMonotonic(result, Abs(matrix[i][j]));
    }
  }
}
// </vc-code>
