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
/* helper modified by LLM (iteration 5): Add exec function to convert spec matrix to exec value */
exec fn get_matrix_value(arr: Matrix<i8>, i: usize, j: usize) -> i8
    requires true
    ensures arr(i, j) == result
{
    arr(i, j)
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
    /* code modified by LLM (iteration 5): Use exec helper function instead of ghost values */
    let mut result = Vec::new();
    let mut i = 0;
    while i < m
        invariant
            i <= m,
            result.len() == i * n,
            forall|row: usize, col: usize| row < i && col < n ==>
                result@[(row * n + col) as int] == arr(row, col)
    {
        let mut j = 0;
        while j < n
            invariant
                i < m,
                j <= n,
                result.len() == i * n + j,
                forall|row: usize, col: usize| row < i && col < n ==>
                    result@[(row * n + col) as int] == arr(row, col),
                forall|col: usize| col < j ==>
                    result@[(i * n + col) as int] == arr(i, col)
        {
            let val = get_matrix_value(arr, i, j);
            result.push(val);
            j += 1;
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}