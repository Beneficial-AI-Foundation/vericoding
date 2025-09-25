// <vc-preamble>
// Matrix represented as sequence of sequences of real numbers
type Matrix = seq<seq<real>>

// Predicate to check if a matrix is square with given dimension
predicate IsSquareMatrix(m: Matrix, n: nat)
{
  |m| == n && n > 0 && forall i :: 0 <= i < n ==> |m[i]| == n
}

// Predicate to check if a matrix is the identity matrix
predicate IsIdentityMatrix(m: Matrix, n: nat)
  requires IsSquareMatrix(m, n)
{
  forall i, j :: 0 <= i < n && 0 <= j < n ==> 
    m[i][j] == (if i == j then 1.0 else 0.0)
}

// Function to perform matrix multiplication
function MatrixMultiply(a: Matrix, b: Matrix, n: nat): Matrix
  requires IsSquareMatrix(a, n) && IsSquareMatrix(b, n)
  ensures IsSquareMatrix(MatrixMultiply(a, b, n), n)
{
  seq(n, i requires 0 <= i < n => 
    seq(n, j requires 0 <= j < n => 
      SumProduct(a[i], GetColumn(b, j, n), n)))
}

// Helper function to compute sum of element-wise products
function SumProduct(row: seq<real>, col: seq<real>, n: nat): real
  requires |row| == n && |col| == n
{
  if n == 0 then 0.0
  else if n == 1 then row[0] * col[0]
  else row[0] * col[0] + SumProduct(row[1..], col[1..], n-1)
}

// Helper function to extract a column from a matrix
function GetColumn(m: Matrix, colIndex: nat, n: nat): seq<real>
  requires IsSquareMatrix(m, n) && colIndex < n
  ensures |GetColumn(m, colIndex, n)| == n
{
  seq(n, i requires 0 <= i < n => m[i][colIndex])
}

// Predicate to check if matrices are equal
predicate MatricesEqual(a: Matrix, b: Matrix, n: nat)
  requires IsSquareMatrix(a, n) && IsSquareMatrix(b, n)
{
  forall i, j :: 0 <= i < n && 0 <= j < n ==> a[i][j] == b[i][j]
}

// Function to compute matrix inverse (specification only)
function {:axiom} MatrixInverse(m: Matrix, n: nat): Matrix
  requires IsSquareMatrix(m, n)
  requires IsInvertible(m, n)
  ensures IsSquareMatrix(MatrixInverse(m, n), n)

// Predicate to check if a matrix is invertible (determinant != 0)
predicate IsInvertible(m: Matrix, n: nat)
  requires IsSquareMatrix(m, n)
{
  // For specification purposes, we define invertibility as the existence of an inverse
  // such that A * A^(-1) = I and A^(-1) * A = I
  exists inv :: IsSquareMatrix(inv, n) && 
    MatricesEqual(MatrixMultiply(m, inv, n), IdentityMatrix(n), n) &&
    MatricesEqual(MatrixMultiply(inv, m, n), IdentityMatrix(n), n)
}

// Function to create identity matrix of given size
function IdentityMatrix(n: nat): Matrix
  requires n > 0
  ensures IsSquareMatrix(IdentityMatrix(n), n)
  ensures IsIdentityMatrix(IdentityMatrix(n), n)
{
  seq(n, i requires 0 <= i < n => 
    seq(n, j requires 0 <= j < n => 
      if i == j then 1.0 else 0.0))
}

/**
 * Raise a square matrix to an integer power following mathematical definitions:
 * - A^0 = Identity matrix
 * - A^1 = A  
 * - A^n = A * A^(n-1) for n > 1
 * - A^(-n) = (A^(-1))^n for n < 0
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MatrixPower(A: Matrix, exp: int, n: nat) returns (result: Matrix)
  requires IsSquareMatrix(A, n)
  requires exp >= 0 || IsInvertible(A, n)  // For negative powers, matrix must be invertible
  ensures IsSquareMatrix(result, n)
  
  // Case 1: Zero power yields identity matrix
  ensures exp == 0 ==> IsIdentityMatrix(result, n)
  
  // Case 2: Power of 1 yields original matrix  
  ensures exp == 1 ==> MatricesEqual(result, A, n)
  
  // Case 3: Power of 2 yields matrix squared
  ensures exp == 2 ==> MatricesEqual(result, MatrixMultiply(A, A, n), n)
  
  // Mathematical properties: dimension preservation
  ensures forall i :: 0 <= i < n ==> |result[i]| == n
  
  // Property: A^0 is always identity regardless of A
  ensures exp == 0 ==> forall i, j :: 0 <= i < n && 0 <= j < n ==> 
    result[i][j] == (if i == j then 1.0 else 0.0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
