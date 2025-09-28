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
/* helper modified by LLM (iteration 5): removed unnecessary external_body helper */
spec fn dummy_fn() {}
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
    /* code modified by LLM (iteration 5): use 'choose' to bridge spec and exec */
    let mut ret = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            i <= m,
            m > 0 && n > 0,
            ret.len() == i * n,
            forall|r: usize, c: usize| r < i && c < n ==>
                ret@[(r * n + c) as int] == matrix_get(arr, r, c),
        decreases m - i
    {
        let mut j: usize = 0;
        while j < n
            invariant
                i < m,
                j <= n,
                m > 0 && n > 0,
                ret.len() == i * n + j,
                forall|r: usize, c: usize|
                    (r < i && c < n) || (r == i && c < j) ==>
                    ret@[(r * n + c) as int] == matrix_get(arr, r, c),
            decreases n - j
        {
            let val = choose|v: i8| v == matrix_get(arr, i, j);
            ret.push(val);
            j = j + 1;
        }
        i = i + 1;
    }
    ret
}
// </vc-code>


}
fn main() {}