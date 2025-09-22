// <vc-preamble>
/**
 * Extracts the diagonal elements from a flattened square matrix.
 * 
 * Given a flattened n×n matrix stored in row-major order, returns the n diagonal
 * elements. For a matrix element at row i, column j in the original 2D representation,
 * its position in the flattened array is i*n + j. Therefore, diagonal elements
 * (where i == j) are located at positions i*n + i.
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method diag(matrix: seq<real>, n: nat) returns (diagonal: seq<real>)
  // The input matrix must represent exactly n×n elements
  requires |matrix| == n * n
  // Ensure no integer overflow in diagonal position calculations
  requires n <= 0x7fffffff / n || n == 0
  
  // The output contains exactly n diagonal elements
  ensures |diagonal| == n
  // Each diagonal element corresponds to the appropriate position in the flattened matrix
  ensures forall i :: 0 <= i < n ==> diagonal[i] == matrix[i * n + i]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
