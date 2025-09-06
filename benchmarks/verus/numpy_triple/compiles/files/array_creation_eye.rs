/* numpy.eye: Return a 2-D array with ones on the diagonal and zeros elsewhere.

Returns the identity matrix of size n x n. For simplicity, we implement 
the square matrix case (N=M) with diagonal offset k=0.

This function creates an n x n matrix where all elements are zero except
for the main diagonal, which contains ones.

Specification: eye returns a square identity matrix with mathematical properties.

Precondition: True (no special preconditions for identity matrix creation)

Postcondition: The returned matrix satisfies:
1. Main diagonal elements are 1.0
2. Off-diagonal elements are 0.0
3. The matrix is square (n x n)
4. Mathematical properties:
   - Symmetry: eye[i][j] = eye[j][i]
   - Uniqueness: There is exactly one 1.0 in each row and column
   - Matrix multiplication identity: For any compatible matrix A, eye * A = A

This captures the complete mathematical characterization of an identity matrix. */

use vstd::prelude::*;

verus! {
fn eye(n: usize) -> (result: Vec<Vec<f64>>)
    requires n > 0,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i].len() == n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> {
            if i == j {
                result[i][j] == 1.0
            } else {
                result[i][j] == 0.0
            }
        },
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> 
            result[i][j] == result[j][i],
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}