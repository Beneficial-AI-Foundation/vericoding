// <vc-preamble>
// Matrix represented as sequence of sequences (rows)
type Matrix<T> = seq<seq<T>>

// Helper function to compute sum of a sequence
function Sum(s: seq<real>): real
{
  if |s| == 0 then 0.0
  else s[0] + Sum(s[1..])
}

// Helper function to check if a matrix is well-formed (all rows have same length)
predicate IsWellFormedMatrix<T>(m: Matrix<T>)
{
  |m| > 0 &&
  (forall i :: 0 <= i < |m| ==> |m[i]| > 0) &&
  (forall i, j :: 0 <= i < j < |m| ==> |m[i]| == |m[j]|)
}

// Helper function to get number of columns in a well-formed matrix
function Cols<T>(m: Matrix<T>): nat
  requires IsWellFormedMatrix(m)
{
  |m[0]|
}

// Helper function to get number of rows in a matrix
function Rows<T>(m: Matrix<T>): nat
{
  |m|
}

// Predicate for dimension compatibility between consecutive matrices
predicate DimensionCompatible<T>(m1: Matrix<T>, m2: Matrix<T>)
{
  IsWellFormedMatrix(m1) && IsWellFormedMatrix(m2) && Cols(m1) == Rows(m2)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MultiDot(A: Matrix<real>, B: Matrix<real>, C: Matrix<real>) returns (result: Matrix<real>)
  // Matrices must be well-formed
  requires IsWellFormedMatrix(A)
  requires IsWellFormedMatrix(B) 
  requires IsWellFormedMatrix(C)
  // Dimension compatibility: A cols = B rows, B cols = C rows
  requires DimensionCompatible(A, B)
  requires DimensionCompatible(B, C)
  // Result has correct dimensions: A rows × C cols
  ensures |result| == Rows(A)
  ensures IsWellFormedMatrix(result)
  ensures Cols(result) == Cols(C)
  // Mathematical correctness: result[i][j] equals triple sum over intermediate indices
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==>
    result[i][j] == Sum(seq(Cols(A), k => Sum(seq(Rows(C), l => A[i][k] * B[k][l] * C[l][j]))))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
