// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
type Matrix = Vec<Vec<i8>>;

spec fn matrix_get(mat: Matrix, i: int, j: int) -> i8
    recommends 
        0 <= i < mat.len(),
        i < mat.len() ==> 0 <= j < mat[i].len()
{
    mat[i][j]
}

spec fn matrix_rows(mat: Matrix) -> int {
    mat.len() as int
}

spec fn matrix_cols(mat: Matrix) -> int
    recommends mat.len() > 0
{
    if mat.len() > 0 { mat[0].len() as int } else { 0 }
}

spec fn matrix_size(mat: Matrix) -> int {
    matrix_rows(mat) * matrix_cols(mat)
}

fn transpose(arr: Matrix) -> (ret: Matrix)
    requires 
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() == arr[0].len(),
    ensures
        ret.len() == arr[0].len(),
        forall|i: int| 0 <= i < ret.len() ==> #[trigger] ret[i].len() == arr.len(),
        matrix_size(ret) == matrix_cols(arr) * matrix_rows(arr),
        forall|i: int, j: int| 
            (0 <= i < matrix_rows(arr) && 0 <= j < matrix_cols(arr)) ==>
            #[trigger] matrix_get(ret, j, i) == matrix_get(arr, i, j)
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