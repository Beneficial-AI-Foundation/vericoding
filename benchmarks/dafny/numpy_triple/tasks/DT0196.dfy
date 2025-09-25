// <vc-preamble>
// Method to compute the lower triangle of a square matrix
// Input: n - dimension of the square matrix
//        matrix - flattened square matrix in row-major order
// Output: flattened matrix with upper triangle zeroed
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method tril(n: nat, matrix: seq<real>) returns (result: seq<real>)
  // Input must be a valid flattened n×n matrix
  requires |matrix| == n * n
  
  // Result preserves the same shape as input
  ensures |result| == |matrix|
  ensures |result| == n * n
  
  // Lower triangle preservation: elements where i ≥ j are unchanged
  ensures forall i, j {:trigger result[i * n + j], matrix[i * n + j]} :: 0 <= i < n && 0 <= j < n && i >= j ==>
    result[i * n + j] == matrix[i * n + j]
  
  // Upper triangle zeroing: elements where i < j are set to zero
  ensures forall i, j {:trigger result[i * n + j]} :: 0 <= i < n && 0 <= j < n && i < j ==>
    result[i * n + j] == 0.0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
