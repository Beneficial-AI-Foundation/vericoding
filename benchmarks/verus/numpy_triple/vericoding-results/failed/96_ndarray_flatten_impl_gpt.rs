// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): row-major index computation as a pure spec function */
spec fn row_major_index(r: int, c: int, width: int) -> int { r * width + c }
/* helper modified by LLM (iteration 5): total length of flattened matrix as a pure spec function */
spec fn total_len(rows: int, cols: int) -> int { rows * cols }
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
{
    /* code modified by LLM (iteration 5): corrected invariants (split comparisons, cast to int in decreases), and implemented row-major flatten */
    let rows = mat.len();
    let cols = mat[0].len();
    let mut res: Vec<f32> = Vec::new();
    let mut r: usize = 0;
    while r < rows
        invariant
            mat.len() == rows,
            rows as int > 0,
            cols as int > 0,
            0 <= r as int,
            r as int <= rows as int,
            forall|i: int| 0 <= i < rows as int ==> mat[i].len() == cols,
            res.len() == r * cols,
            forall|i: int, j: int|
                0 <= i < r as int && 0 <= j < cols as int ==>
                res@[(i * (cols as int) + j)] == mat[i][j]
        decreases rows as int - r as int
    {
        let mut c: usize = 0;
        while c < cols
            invariant
                mat.len() == rows,
                rows as int > 0,
                cols as int > 0,
                0 <= r as int,
                r as int < rows as int,
                0 <= c as int,
                c as int <= cols as int,
                forall|i: int| 0 <= i < rows as int ==> mat[i].len() == cols,
                res.len() == r * cols + c,
                forall|j: int|
                    0 <= j < c as int ==>
                    res@[(r as int) * (cols as int) + j] == mat[r as int][j],
                forall|i: int, j: int|
                    0 <= i < r as int && 0 <= j < cols as int ==>
                    res@[(i * (cols as int) + j)] == mat[i][j]
            decreases cols as int - c as int
        {
            let v = mat[r][c];
            res.push(v);
            c = c + 1;
        }
        r = r + 1;
    }
    res
}
// </vc-code>

}
fn main() {}