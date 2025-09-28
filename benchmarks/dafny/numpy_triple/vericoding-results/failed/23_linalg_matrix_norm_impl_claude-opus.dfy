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
/* helper modified by LLM (iteration 5): Fixed SquareZeroImpliesZero and ElementBoundedBySqrt lemmas */
lemma SumOfSquaresNonNegative(matrix: seq<seq<real>>)
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  ensures SumOfSquares(matrix) >= 0.0
{
  if |matrix| == 0 {
    assert SumOfSquares(matrix) == 0.0;
  } else {
    SumOfSquaresRowNonNegative(matrix[0]);
    SumOfSquaresNonNegative(matrix[1..]);
  }
}

lemma SumOfSquaresRowNonNegative(row: seq<real>)
  ensures SumOfSquaresRow(row) >= 0.0
{
  if |row| == 0 {
    assert SumOfSquaresRow(row) == 0.0;
  } else {
    assert row[0] * row[0] >= 0.0;
    SumOfSquaresRowNonNegative(row[1..]);
  }
}

lemma SumOfSquaresZeroIffAllZero(matrix: seq<seq<real>>)
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  requires |matrix| > 0 && |matrix[0]| > 0
  ensures SumOfSquares(matrix) == 0.0 <==> AllZero(matrix)
{
  if SumOfSquares(matrix) == 0.0 {
    SumZeroImpliesAllZero(matrix);
  }
  if AllZero(matrix) {
    AllZeroImpliesSumZero(matrix);
  }
}

lemma SumZeroImpliesAllZero(matrix: seq<seq<real>>)
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  requires |matrix| > 0 && |matrix[0]| > 0
  requires SumOfSquares(matrix) == 0.0
  ensures AllZero(matrix)
{
  if |matrix| == 1 {
    SumZeroImpliesRowZero(matrix[0]);
  } else {
    SumOfSquaresRowNonNegative(matrix[0]);
    SumOfSquaresNonNegative(matrix[1..]);
    assert SumOfSquaresRow(matrix[0]) == 0.0;
    assert SumOfSquares(matrix[1..]) == 0.0;
    SumZeroImpliesRowZero(matrix[0]);
    if |matrix[1..]| > 0 && |matrix[1..][0]| > 0 {
      SumZeroImpliesAllZero(matrix[1..]);
    }
  }
}

lemma SumZeroImpliesRowZero(row: seq<real>)
  requires |row| > 0
  requires SumOfSquaresRow(row) == 0.0
  ensures forall j :: 0 <= j < |row| ==> row[j] == 0.0
{
  if |row| == 1 {
    assert SumOfSquaresRow(row) == row[0] * row[0];
    assert row[0] * row[0] == 0.0;
    SquareZeroImpliesZero(row[0]);
  } else {
    assert SumOfSquaresRow(row) == row[0] * row[0] + SumOfSquaresRow(row[1..]);
    assert row[0] * row[0] >= 0.0;
    SumOfSquaresRowNonNegative(row[1..]);
    assert SumOfSquaresRow(row[1..]) >= 0.0;
    assert row[0] * row[0] == 0.0;
    SquareZeroImpliesZero(row[0]);
    assert SumOfSquaresRow(row[1..]) == 0.0;
    SumZeroImpliesRowZero(row[1..]);
  }
}

lemma SquareZeroImpliesZero(x: real)
  requires x * x == 0.0
  ensures x == 0.0
{
  if x != 0.0 {
    if x > 0.0 {
      assert x * x > 0.0;
    } else {
      assert x < 0.0;
      assert x * x > 0.0;
    }
  }
}

lemma AllZeroImpliesSumZero(matrix: seq<seq<real>>)
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  requires AllZero(matrix)
  ensures SumOfSquares(matrix) == 0.0
{
  if |matrix| == 0 {
    assert SumOfSquares(matrix) == 0.0;
  } else {
    forall j | 0 <= j < |matrix[0]|
      ensures matrix[0][j] == 0.0
    {
      assert matrix[0][j] == 0.0;
    }
    AllZeroImpliesRowSumZero(matrix[0]);
    if |matrix| > 1 {
      assert AllZero(matrix[1..]);
      AllZeroImpliesSumZero(matrix[1..]);
    }
  }
}

lemma AllZeroImpliesRowSumZero(row: seq<real>)
  requires forall j :: 0 <= j < |row| ==> row[j] == 0.0
  ensures SumOfSquaresRow(row) == 0.0
{
  if |row| == 0 {
    assert SumOfSquaresRow(row) == 0.0;
  } else {
    assert row[0] == 0.0;
    assert row[0] * row[0] == 0.0;
    AllZeroImpliesRowSumZero(row[1..]);
  }
}

function ComputeSumOfSquares(matrix: seq<seq<real>>): real
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  ensures ComputeSumOfSquares(matrix) == SumOfSquares(matrix)
  decreases |matrix|
{
  if |matrix| == 0 then 0.0
  else ComputeSumOfSquaresRow(matrix[0]) + ComputeSumOfSquares(matrix[1..])
}

function ComputeSumOfSquaresRow(row: seq<real>): real
  ensures ComputeSumOfSquaresRow(row) == SumOfSquaresRow(row)
  decreases |row|
{
  if |row| == 0 then 0.0
  else row[0] * row[0] + ComputeSumOfSquaresRow(row[1..])
}

function Sqrt(x: real): real
  requires x >= 0.0
  ensures Sqrt(x) >= 0.0
  ensures Sqrt(x) * Sqrt(x) == x

lemma ElementBoundedBySqrt(matrix: seq<seq<real>>, i: int, j: int, sqrtSum: real)
  requires forall k :: 0 <= k < |matrix| ==> |matrix[k]| == |matrix[0]|
  requires 0 <= i < |matrix| && 0 <= j < |matrix[i]|
  requires sqrtSum >= 0.0
  requires sqrtSum * sqrtSum == SumOfSquares(matrix)
  ensures Abs(matrix[i][j]) <= sqrtSum
{
  assert matrix[i][j] * matrix[i][j] >= 0.0;
  ElementInSumOfSquares(matrix, i, j);
  assert matrix[i][j] * matrix[i][j] <= SumOfSquares(matrix);
  assert matrix[i][j] * matrix[i][j] <= sqrtSum * sqrtSum;
  if Abs(matrix[i][j]) > sqrtSum {
    if matrix[i][j] >= 0.0 {
      assert Abs(matrix[i][j]) == matrix[i][j];
      assert matrix[i][j] > sqrtSum;
      assert matrix[i][j] * matrix[i][j] > sqrtSum * sqrtSum;
    } else {
      assert Abs(matrix[i][j]) == -matrix[i][j];
      assert -matrix[i][j] > sqrtSum;
      assert matrix[i][j] < -sqrtSum;
      assert matrix[i][j] * matrix[i][j] > sqrtSum * sqrtSum;
    }
  }
}

lemma ElementInSumOfSquares(matrix: seq<seq<real>>, i: int, j: int)
  requires forall k :: 0 <= k < |matrix| ==> |matrix[k]| == |matrix[0]|
  requires 0 <= i < |matrix| && 0 <= j < |matrix[i]|
  ensures matrix[i][j] * matrix[i][j] <= SumOfSquares(matrix)
{
  if i == 0 {
    ElementInRowSum(matrix[0], j);
    SumOfSquaresNonNegative(matrix[1..]);
  } else {
    ElementInSumOfSquares(matrix[1..], i-1, j);
    SumOfSquaresRowNonNegative(matrix[0]);
  }
}

lemma ElementInRowSum(row: seq<real>, j: int)
  requires 0 <= j < |row|
  ensures row[j] * row[j] <= SumOfSquaresRow(row)
{
  if j == 0 {
    SumOfSquaresRowNonNegative(row[1..]);
  } else {
    ElementInRowSum(row[1..], j-1);
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
/* code modified by LLM (iteration 5): Implementation computing Frobenius norm */
{
  if |matrix| == 0 || |matrix[0]| == 0 {
    result := 0.0;
    return;
  }
  
  var sum := ComputeSumOfSquares(matrix);
  SumOfSquaresNonNegative(matrix);
  assert sum >= 0.0;
  result := Sqrt(sum);
  
  assert result >= 0.0;
  assert result * result == sum;
  assert sum == SumOfSquares(matrix);
  assert result * result == SumOfSquares(matrix);
  
  SumOfSquaresZeroIffAllZero(matrix);
  assert SumOfSquares(matrix) == 0.0 <==> AllZero(matrix);
  assert result * result == 0.0 <==> AllZero(matrix);
  
  if result == 0.0 {
    assert result * result == 0.0;
    assert SumOfSquares(matrix) == 0.0;
    assert AllZero(matrix);
  }
  
  if AllZero(matrix) {
    assert SumOfSquares(matrix) == 0.0;
    assert result * result == 0.0;
    SquareZeroImpliesZero(result);
    assert result == 0.0;
  }
  
  assert result == 0.0 <==> AllZero(matrix);
  
  forall i, j | 0 <= i < |matrix| && 0 <= j < |matrix[i]|
    ensures Abs(matrix[i][j]) <= result
  {
    ElementBoundedBySqrt(matrix, i, j, result);
  }
  
  if HasNonZero(matrix) {
    assert !AllZero(matrix);
    assert result != 0.0;
    assert result > 0.0;
  }
}
// </vc-code>
