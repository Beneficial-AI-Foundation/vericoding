// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Matrix type definition: function from row,col indices to values */
type Matrix<T> = spec_fn(usize, usize) -> T;

/* Get matrix element at position (i,j) */
spec fn matrix_get<T>(mat: Matrix<T>, i: usize, j: usize) -> T {
    mat(i, j)
}

/* Matrix size helper */
spec fn matrix_size(m: usize, n: usize) -> usize {
    (m * n) as usize
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn ravel(arr: Matrix<i8>, m: usize, n: usize) -> (ret: Vec<i8>)
    requires m > 0 && n > 0,
    ensures 
        ret.len() == m * n,
        forall|i: usize, j: usize| i < m && j < n ==> 
            ret@[(i * n + j) as int] == matrix_get(arr, i, j)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}