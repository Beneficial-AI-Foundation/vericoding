/* Compute the eigenvalues of a complex Hermitian or real symmetric matrix

Main difference from eigh: Does not compute eigenvectors.

Parameters:
- a: Hermitian or symmetric matrix
- UPLO: Use upper or lower triangular part

Returns:
- w: The eigenvalues in ascending order

Compute the eigenvalues of a real symmetric matrix.
Returns eigenvalues in ascending order without computing eigenvectors.
This is the eigenvalues-only version of the symmetric eigenvalue problem.

Specification: eigvalsh computes eigenvalues of a real symmetric matrix.

The eigenvalues are real (since the matrix is symmetric) and returned in ascending order.
Key mathematical properties:
1. The eigenvalues are real for symmetric matrices
2. They are returned in ascending order
3. The trace equals the sum of eigenvalues
4. The determinant equals the product of eigenvalues
5. For the identity matrix, all eigenvalues are 1
6. For diagonal matrices, eigenvalues are the diagonal elements (sorted)
7. Matrix symmetry: a[i][j] = a[j][i] for all i,j */

use vstd::prelude::*;

verus! {
fn eigvalsh(a: Vec<Vec<f64>>, n: usize) -> (eigenvals: Vec<f64>)
    requires
        n > 0,
        a.len() == n,
        forall|i: int| 0 <= i < n ==> a[i].len() == n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> a[i][j] == a[j][i],
    ensures
        eigenvals.len() == n,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}