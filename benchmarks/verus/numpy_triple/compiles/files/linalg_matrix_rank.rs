/* numpy.linalg.matrix_rank: Return matrix rank of array using SVD method.
    
The rank of a matrix is the number of linearly independent columns
(or rows). For numerical computation, this is determined by counting
the number of singular values greater than a threshold.

This implementation focuses on the core mathematical behavior for
square matrices, using default tolerance.

Specification: matrix_rank computes the rank of a matrix using SVD method.

The rank is the number of singular values greater than a numerical threshold.
This corresponds to the number of linearly independent columns (or rows).

Mathematical definition:
- For a matrix A, rank(A) = number of non-zero singular values
- In numerical computation, "non-zero" means above a threshold

Key properties verified:
1. Bounds: 0 ≤ rank(A) ≤ min(m, n) for m×n matrix
2. Zero matrix: rank(0) = 0 (all elements zero)
3. Identity matrix: rank(I) = n for n×n identity matrix
4. Rank deficiency: If a row/column is all zeros, rank < full rank
5. Linear dependence: If rows/columns are linearly dependent, rank < full rank

The threshold behavior ensures numerical stability but is not explicitly
specified here for simplicity. */

use vstd::prelude::*;

verus! {
spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn all_zero_row(a: &Vec<Vec<f64>>, i: int) -> bool {
    forall|j: int| 0 <= j < a[0].len() ==> a[i][j] == 0.0
}

spec fn all_zero_col(a: &Vec<Vec<f64>>, j: int) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i][j] == 0.0
}

spec fn rows_equal(a: &Vec<Vec<f64>>, i1: int, i2: int) -> bool {
    forall|j: int| 0 <= j < a[0].len() ==> a[i1][j] == a[i2][j]
}

spec fn cols_equal(a: &Vec<Vec<f64>>, j1: int, j2: int) -> bool {
    forall|i: int| 0 <= i < a.len() ==> a[i][j1] == a[i][j2]
}
fn matrix_rank(a: &Vec<Vec<f64>>) -> (result: usize)
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i].len() > 0,
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i].len() == a[j].len(),
    ensures 
        result <= min(a.len() as int, a[0].len() as int),
        (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[0].len() ==> a[i][j] == 0.0) ==> result == 0,
        (exists|i: int| 0 <= i < a.len() && all_zero_row(a, i)) ==> result < a.len(),
        (exists|j: int| 0 <= j < a[0].len() && all_zero_col(a, j)) ==> result < a[0].len(),
        (a.len() > 1) ==> 
            (exists|i1: int, i2: int| 0 <= i1 < a.len() && 0 <= i2 < a.len() && i1 != i2 && 
                rows_equal(a, i1, i2)) ==> result < a.len(),
        (a[0].len() > 1) ==>
            (exists|j1: int, j2: int| 0 <= j1 < a[0].len() && 0 <= j2 < a[0].len() && j1 != j2 && 
                cols_equal(a, j1, j2)) ==> result < a[0].len(),
{
    // impl-start
    assume(false);
    0
    // impl-end
}
}
fn main() {}