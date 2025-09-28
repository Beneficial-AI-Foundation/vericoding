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
/* helper modified by LLM (iteration 5): define pure ravel sequence without requires/ensures; safe even when n == 0 */
spec fn ravel_seq(arr: Matrix<i8>, m: usize, n: usize) -> Seq<i8> {
    Seq::new((m * n) as nat, |k: int| {
        if n == 0 {
            0i8
        } else {
            let ni: int = n as int;
            let ii: usize = (k / ni) as usize;
            let jj: usize = (k % ni) as usize;
            matrix_get(arr, ii, jj)
        }
    })
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
    /* code modified by LLM (iteration 5): construct Vec in row-major order with loop invariants ensuring content mapping */
    let mut v: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            m > 0,
            n > 0,
            i <= m,
            v.len() == i * n,
            forall|ii: usize, jj: usize|
                ii < i && jj < n ==> v@[((ii * n + jj) as int)] == matrix_get(arr, ii, jj),
        decreases m - i
    {
        let mut j: usize = 0;
        while j < n
            invariant
                m > 0,
                n > 0,
                i < m,
                j <= n,
                v.len() == i * n + j,
                forall|ii: usize, jj: usize|
                    ii < i && jj < n ==> v@[((ii * n + jj) as int)] == matrix_get(arr, ii, jj),
                forall|jj: usize|
                    jj < j ==> v@[((i * n + jj) as int)] == matrix_get(arr, i, jj),
            decreases n - j
        {
            v.push(matrix_get(arr, i, j));
            j = j + 1;
        }
        i = i + 1;
    }
    v
}
// </vc-code>


}
fn main() {}