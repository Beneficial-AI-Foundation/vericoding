/* An array with ones at and below the given diagonal and zeros elsewhere.
    
Creates a matrix of shape (N, M) where T[i,j] = 1 if j ≤ i + k, and 0 otherwise.
The parameter k controls the diagonal: k = 0 is the main diagonal,
k < 0 is below it, and k > 0 is above it.

Specification: tri creates a lower triangular matrix with specified diagonal offset.
    
The resulting matrix has ones at and below the k-th diagonal, zeros elsewhere.
For each position (i, j):
- If j ≤ i + k, then the value is 1.0
- Otherwise, the value is 0.0
    
This captures the mathematical property that defines a generalized lower triangular matrix. */

use vstd::prelude::*;

verus! {
fn tri(n: usize, m: usize, k: i32) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i].len() == m,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < m ==> 
            result[i][j] == if j <= i + k { 1.0 } else { 0.0 },
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}