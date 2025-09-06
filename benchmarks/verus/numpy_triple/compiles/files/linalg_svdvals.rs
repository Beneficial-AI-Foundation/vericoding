/* numpy.linalg.svdvals: Compute singular values of a matrix.

   Computes the singular values of a matrix without computing the U and V matrices.
   The singular values are the square roots of the eigenvalues of A^T @ A (or A @ A^T),
   returned in descending order.
   
   This is equivalent to calling numpy.linalg.svd(x, compute_uv=False).
   For an m×n matrix, this returns min(m,n) singular values.
*/

/* Specification: svdvals returns the singular values of the input matrix.

   The singular values are:
   1. Non-negative real numbers
   2. Sorted in descending order
   3. Square roots of eigenvalues of x^T @ x
   4. Measure the "magnitude" of the matrix in each singular direction
   
   Precondition: True (singular values are defined for any matrix)
   Postcondition: Returns singular values in descending order with mathematical properties
*/
use vstd::prelude::*;

verus! {
// <vc-helpers>
spec fn min(a: usize, b: usize) -> usize {
    if a <= b { a } else { b }
}
// </vc-helpers>
fn svdvals(x: Vec<Vec<f64>>) -> (result: Vec<f64>)
    requires x.len() > 0 && (forall|i: int| 0 <= i < x.len() ==> x[i].len() > 0),
    ensures result.len() <= x.len() && (forall|i: int| 0 <= i < x.len() ==> result.len() <= x[i].len()),
// <vc-implementation>
{
    return Vec::new(); // TODO: Remove this line and implement the function body
}
// </vc-implementation>
proof fn svdvals_spec(x: Vec<Vec<f64>>)
    requires x.len() > 0 && (forall|i: int| 0 <= i < x.len() ==> x[i].len() > 0),
{
    /* Property 1: All singular values are non-negative */
    /* Property 2: Singular values are sorted in descending order */
    /* Property 3: Singular values are bounded by the Frobenius norm */
    /* Property 4: If the matrix is zero, all singular values are zero */
    /* Property 5: The sum of squares of singular values equals the Frobenius norm squared */
// <vc-proof>
    assume(false); // TODO: Remove this line and implement the proof
// </vc-proof>
}

fn main() {}

}