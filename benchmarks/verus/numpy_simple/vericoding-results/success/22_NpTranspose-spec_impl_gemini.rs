// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): No helpers are needed for this implementation. */
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
    /* code modified by LLM (iteration 4): Added an invariant about matrix_size to the outer loop to help prove the final postcondition. */
    let rows = arr.len();
    let cols = arr[0].len();

    let mut ret: Matrix = Vec::new();

    let mut j: usize = 0;
    while j < cols
        invariant
            arr.len() > 0,
            rows == arr.len(),
            cols == arr[0].len(),
            forall|i: int| 0 <= i < rows ==> arr[i].len() == cols,
            0 <= j <= cols,
            ret.len() == j,
            forall|y: int| 0 <= y < j ==> ret[y].len() == rows,
            matrix_size(ret) == j * rows,
            forall|y: int, x: int|
                (0 <= y < j && 0 <= x < rows) ==>
                ret[y][x] == arr[x][y],
        decreases cols - j
    {
        let mut new_row: Vec<i8> = Vec::new();
        let mut i: usize = 0;
        while i < rows
            invariant
                arr.len() > 0,
                rows == arr.len(),
                cols == arr[0].len(),
                forall|k: int| 0 <= k < rows ==> arr[k].len() == cols,
                0 <= j < cols,
                0 <= i <= rows,
                new_row.len() == i,
                forall|k: int| 0 <= k < i ==> new_row[k] == arr[k][j as int],
            decreases rows - i
        {
            new_row.push(arr[i][j]);
            i = i + 1;
        }
        ret.push(new_row);
        j = j + 1;
    }
    ret
}
// </vc-code>


}
fn main() {}