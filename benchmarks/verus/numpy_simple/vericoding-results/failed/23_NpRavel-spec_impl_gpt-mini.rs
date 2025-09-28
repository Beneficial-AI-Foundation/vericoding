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
/* helper modified by LLM (iteration 5): compute linear index from row and column */
spec fn idx(i: usize, j: usize, n: usize) -> int {
    (i * n + j) as int
}

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
    /* code modified by LLM (iteration 5): build Vec by pushing matrix elements row-major with invariants */
    let mut v: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            v.len() == i * n,
            forall|ii: usize, jj: usize| ii < i && jj < n ==> v@[idx(ii, jj, n)] == matrix_get(arr, ii, jj),
        decreases m - i
    {
        let mut j: usize = 0;
        while j < n
            invariant
                v.len() == i * n + j,
                forall|ii: usize, jj: usize| ((ii < i) || (ii == i && jj < j)) && ii < m && jj < n ==> v@[idx(ii, jj, n)] == matrix_get(arr, ii, jj),
            decreases n - j
        {
            v.push(matrix_get(arr, i, j));
            j += 1;
        }
        i += 1;
    }
    v
}

// </vc-code>


}
fn main() {}