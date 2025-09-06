/*
{
  "name": "numpy.diag",
  "category": "Diagonal operations", 
  "description": "Extract a diagonal or construct a diagonal array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.diag.html",
  "doc": "Extract a diagonal or construct a diagonal array.\n\nParameters\n----------\nv : array_like\n    If `v` is a 2-D array, return a copy of its `k`-th diagonal.\n    If `v` is a 1-D array, return a 2-D array with `v` on the `k`-th diagonal.\nk : int, optional\n    Diagonal in question. The default is 0. Use `k>0` for diagonals above the main diagonal, and `k<0` for diagonals below the main diagonal.\n\nReturns\n-------\nout : ndarray\n    The extracted diagonal or constructed diagonal array.",
}
*/

/* numpy.diag: Extract a diagonal or construct a diagonal array.
   
   For simplicity, this specification focuses on extracting the diagonal
   from a square matrix represented as a flattened vector.
   Given a flattened n×n matrix, returns the diagonal elements.
   
   This specification captures the essential mathematical property of
   diagonal extraction in a type-safe manner using Vector types.
*/

/* Specification: diag extracts diagonal elements from a flattened matrix.
   
   Mathematical Properties:
   1. Diagonal Extraction: For a flattened n×n matrix stored in row-major order,
      the diagonal elements are located at positions i*n + i for i ∈ [0, n).
   
   2. Type Safety: The function maintains type safety by using Vector types
      that encode the size information at the type level.
   
   3. Correctness: Each element in the result vector corresponds to a diagonal
      element from the original matrix, preserving the mathematical structure.
   
   This specification provides a foundation for formal verification of diagonal
   operations in numerical computing.
*/
use vstd::prelude::*;

verus! {
// <vc-helpers>
// </vc-helpers>
spec fn diag(n: usize, matrix: Vec<f64>) -> Vec<f64>
// <vc-implementation>
{
    arbitrary() // TODO: Remove this line and implement the function body
}
// </vc-implementation>
proof fn diag_spec(n: usize, matrix: Vec<f64>)
    requires
        matrix.len() == n * n,
    ensures
        diag(n, matrix).len() == n,
        forall|i: int| 0 <= i < n ==> diag(n, matrix)[i] == matrix[i * (n as int) + i],
// <vc-proof>
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-proof>
fn main() {}

}