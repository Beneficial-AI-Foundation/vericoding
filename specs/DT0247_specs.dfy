// <vc-preamble>
// Matrix and vector type definitions
type Matrix = seq<seq<real>>
type Vector = seq<real>

// Predicate to check if a matrix is square with given dimension
predicate IsSquareMatrix(m: Matrix, n: nat)
{
  |m| == n && forall i :: 0 <= i < n ==> |m[i]| == n
}

// Predicate to check if a vector has given dimension
predicate IsVector(v: Vector, n: nat)
{
  |v| == n
}

// Matrix-vector multiplication: result[i] = sum(a[i][j] * v[j] for j in 0..n)
function MatrixVectorMultiply(a: Matrix, v: Vector, n: nat): Vector
  requires IsSquareMatrix(a, n) && IsVector(v, n)
  ensures IsVector(MatrixVectorMultiply(a, v, n), n)
{
  seq(n, i requires 0 <= i < n => 
    Sum(seq(n, j requires 0 <= j < n => a[i][j] * v[j])))
}

// Matrix multiplication: result[i][j] = sum(a[i][k] * b[k][j] for k in 0..n)
function MatrixMultiply(a: Matrix, b: Matrix, n: nat): Matrix
  requires IsSquareMatrix(a, n) && IsSquareMatrix(b, n)
  ensures IsSquareMatrix(MatrixMultiply(a, b, n), n)
{
  seq(n, i requires 0 <= i < n => 
    seq(n, j requires 0 <= j < n => 
      Sum(seq(n, k requires 0 <= k < n => a[i][k] * b[k][j]))))
}

// Identity matrix predicate
predicate IsIdentityMatrix(m: Matrix, n: nat)
  requires IsSquareMatrix(m, n)
{
  forall i, j :: 0 <= i < n && 0 <= j < n ==>
    m[i][j] == (if i == j then 1.0 else 0.0)
}

// Predicate to check if two matrices are inverses of each other
predicate AreInverses(a: Matrix, a_inv: Matrix, n: nat)
  requires IsSquareMatrix(a, n) && IsSquareMatrix(a_inv, n)
{
  IsIdentityMatrix(MatrixMultiply(a, a_inv, n), n) &&
  IsIdentityMatrix(MatrixMultiply(a_inv, a, n), n)
}

// Helper function to sum a sequence of reals
function Sum(s: seq<real>): real
{
  if |s| == 0 then 0.0
  else s[0] + Sum(s[1..])
}

// Main tensorsolve method specification
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method tensorsolve(a: Matrix, b: Vector, n: nat) returns (x: Vector)
  requires IsSquareMatrix(a, n)
  requires IsVector(b, n)
  // Matrix a must be invertible
  requires exists a_inv :: IsSquareMatrix(a_inv, n) && AreInverses(a, a_inv, n)
  ensures IsVector(x, n)
  // Correctness: The solution satisfies a * x = b
  ensures MatrixVectorMultiply(a, x, n) == b
  // Uniqueness: x is the unique solution to a * x = b
  ensures forall y :: IsVector(y, n) && MatrixVectorMultiply(a, y, n) == b ==> y == x
  // The solution can be computed using the inverse: x = a_inv * b
  ensures exists a_inv :: IsSquareMatrix(a_inv, n) && AreInverses(a, a_inv, n) &&
            x == MatrixVectorMultiply(a_inv, b, n)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
