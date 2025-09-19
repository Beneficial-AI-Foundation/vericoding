// <vc-preamble>
/*
 * Dafny specification for computing eigenvalues of a general square matrix.
 * This module provides a specification-only interface for eigenvalue computation
 * equivalent to numpy.linalg.eigvals functionality.
 */

// Complex number representation for eigenvalues
datatype Complex = Complex(re: real, im: real)

// Helper predicate to check if a matrix is square
predicate IsSquareMatrix<T>(matrix: seq<seq<T>>) 
{
    |matrix| > 0 && forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix|
}

// Helper predicate to check if a matrix is diagonal
predicate IsDiagonal(matrix: seq<seq<real>>)
    requires IsSquareMatrix(matrix)
{
    forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[i]| && i != j ==> matrix[i][j] == 0.0
}

// Helper predicate to check if a complex number appears in a sequence
predicate ContainsComplex(eigenvalues: seq<Complex>, value: Complex)
{
    exists k :: 0 <= k < |eigenvalues| && eigenvalues[k] == value
}

// Method to compute eigenvalues of a square matrix
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Eigvals(matrix: seq<seq<real>>) returns (eigenvalues: seq<Complex>)
    requires IsSquareMatrix(matrix)
    requires |matrix| >= 1
    ensures |eigenvalues| == |matrix|
    // For diagonal matrices, eigenvalues are the diagonal elements with zero imaginary part
    ensures IsDiagonal(matrix) ==> 
        forall i :: 0 <= i < |matrix| ==> 
            ContainsComplex(eigenvalues, Complex(matrix[i][i], 0.0))
    // The result contains exactly the right number of eigenvalues
    ensures |eigenvalues| == |matrix|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
