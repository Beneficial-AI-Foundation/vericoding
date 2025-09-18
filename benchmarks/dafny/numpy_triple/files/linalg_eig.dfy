// <vc-preamble>
/*
 * Eigenvalue and Eigenvector Computation Specification
 * 
 * This file specifies the computation of eigenvalues and right eigenvectors 
 * of a square matrix, satisfying the fundamental eigenvalue equation A*v = λ*v.
 */

// Helper function to compute dot product of two vectors
function DotProduct(v1: seq<real>, v2: seq<real>): real
  requires |v1| == |v2|
{
  if |v1| == 0 then 0.0 else v1[0] * v2[0] + DotProduct(v1[1..], v2[1..])
}

// Helper function to multiply matrix A by vector v
function MatrixVectorMultiply(A: seq<seq<real>>, v: seq<real>): seq<real>
  requires |A| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A|
  requires |v| == |A|
{
  seq(|A|, i => DotProduct(A[i], v))
}

// Helper function to scale vector v by scalar s
function ScaleVector(v: seq<real>, s: real): seq<real>
{
  seq(|v|, i => v[i] * s)
}

// Helper function to compute vector norm squared
function VectorNormSquared(v: seq<real>): real
{
  DotProduct(v, v)
}

// Helper predicate to check if matrix is diagonal
predicate IsDiagonal(A: seq<seq<real>>)
  requires |A| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A|
{
  forall i, j :: 0 <= i < |A| && 0 <= j < |A| && i != j ==> A[i][j] == 0.0
}

// Helper predicate to check if matrix is identity
predicate IsIdentity(A: seq<seq<real>>)
  requires |A| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A|
{
  forall i, j :: 0 <= i < |A| && 0 <= j < |A| ==> 
    A[i][j] == (if i == j then 1.0 else 0.0)
}

// Helper function to extract column i from matrix of eigenvectors
function GetColumn(eigenvectors: seq<seq<real>>, col: int): seq<real>
  requires |eigenvectors| > 0
  requires forall i :: 0 <= i < |eigenvectors| ==> |eigenvectors[i]| == |eigenvectors|
  requires 0 <= col < |eigenvectors|
{
  seq(|eigenvectors|, i => eigenvectors[i][col])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ComputeEigenvalues(A: seq<seq<real>>) returns (eigenvalues: seq<real>, eigenvectors: seq<seq<real>>)
  // Input matrix must be square and non-empty
  requires |A| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A|
  
  // Output dimensions match input
  ensures |eigenvalues| == |A|
  ensures |eigenvectors| == |A|
  ensures forall i :: 0 <= i < |eigenvectors| ==> |eigenvectors[i]| == |A|
  
  // Main eigenvalue equation: A * v_i = λ_i * v_i for each eigenvalue-eigenvector pair
  ensures forall i :: 0 <= i < |A| ==>
    var v_i := GetColumn(eigenvectors, i);
    var lambda_i := eigenvalues[i];
    MatrixVectorMultiply(A, v_i) == ScaleVector(v_i, lambda_i)
  
  // For diagonal matrices, eigenvalues are the diagonal elements (allowing permutation)
  ensures IsDiagonal(A) ==>
    forall i :: 0 <= i < |A| ==> exists j :: 0 <= j < |eigenvalues| && eigenvalues[j] == A[i][i]
  
  // Identity matrix has eigenvalue 1 with multiplicity n
  ensures IsIdentity(A) ==>
    forall i :: 0 <= i < |A| ==> eigenvalues[i] == 1.0
  
  // Eigenvectors are non-zero (at least one component is non-zero)
  ensures forall i :: 0 <= i < |A| ==>
    var v_i := GetColumn(eigenvectors, i);
    exists j :: 0 <= j < |v_i| && v_i[j] != 0.0
  
  // Eigenvectors are normalized (unit length)
  ensures forall i :: 0 <= i < |A| ==>
    var v_i := GetColumn(eigenvectors, i);
    VectorNormSquared(v_i) == 1.0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
