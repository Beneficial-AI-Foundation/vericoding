// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn flatten(mat: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        mat.len() > 0,
        forall|i: int| 0 <= i < mat.len() ==> mat[i].len() > 0,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat.len() ==> mat[i].len() == mat[j].len(),
    ensures 
        result.len() == mat.len() * mat[0].len(),
        forall|r: int, c: int| 
            0 <= r < mat.len() && 0 <= c < mat[0].len() ==>
            result[r * mat[0].len() + c] == mat[r][c]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type casting to allow `int` variables only in ghost context and `usize` for array indexing. */
{
    let rows_usize: usize = mat.len();
    let cols_usize: usize = mat[0].len();
    let rows: int = rows_usize as int;
    let cols: int = cols_usize as int;

    let mut result: Vec<f32> = Vec::with_capacity(rows_usize * cols_usize);
    let mut i: usize = 0;
    while i < rows_usize
        invariant
            i <= rows_usize,
            result.len() == i * cols_usize,
            forall|r: int, c: int|
                0 <= r < i as int && 0 <= c < cols as int ==> result[(r * cols + c) as usize] == mat[r as usize][c as usize],
    {
        let mut j: usize = 0;
        while j < cols_usize
            invariant
                j <= cols_usize,
                result.len() == (i * cols_usize + j),
                forall|r: int, c: int|
                    0 <= r < i as int && 0 <= c < cols as int ==> result[(r * cols + c) as usize] == mat[r as usize][c as usize],
                forall|c: int|
                    0 <= c < j as int ==> result[(i as int * cols + c) as usize] == mat[i as usize][c as usize],
        {
            result.push(mat[i][j]);
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}