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
/* helper modified by LLM (iteration 5): Added invariants and convergence check to avoid division by zero and improve approximation proof */
method Sqrt(x: real) returns (r: real)
  requires x >= 0.0
  ensures r >= 0.0
  ensures Abs(r * r - x) <= 0.001
{
  if x == 0.0 {
    r := 0.0;
    return;
  }
  r := (x + 1.0) / 2.0;
  var old_r := r + 1.0;
  var i := 0;
  while i < 100 && Abs(r - old_r) > 0.0001
    invariant r > 0.0
    invariant old_r > 0.0
  {
    old_r := r;
    r := (r + x / r) / 2.0;
    i := i + 1;
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
/* code modified by LLM (iteration 5): Kept the calculation of sum of squares with invariants, calling Sqrt for approximation */
{
  if |matrix| == 0 {
    result := 0.0;
    return;
  }
  var sum : real := 0.0;
  var i : int := 0;
  while i < |matrix|
    invariant 0 <= i <= |matrix|
    invariant sum >= 0.0
    decreases |matrix| - i
  {
    var j : int := 0;
    while j < |matrix[i]|
      invariant 0 <= j <= |matrix[i]|
      invariant sum >= 0.0
      decreases |matrix[i]| - j
    {
      sum := sum + matrix[i][j] * matrix[i][j];
      j := j + 1;
    }
    i := i + 1;
  }
  var sqrt_sum : real := Sqrt(sum);
  result := sqrt_sum;
}
// </vc-code>
