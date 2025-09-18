// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute coordinate from index using int->f32 casts */
fn idx_to_coord(start: f32, stop: f32, n: int, idx: int) -> f32 { if n == 1 { start } else { start + (stop - start) * ((idx as f32) / ((n - 1) as f32)) } }
// </vc-helpers>

// <vc-spec>
type Matrix = Vec<Vec<f32>>;

fn mgrid(rows: usize, cols: usize, start_r: f32, stop_r: f32, start_c: f32, stop_c: f32) -> (result: (Matrix, Matrix))
    requires rows > 0 && cols > 0,
    ensures 
        result.0.len() == rows && result.1.len() == rows,
        forall|i: int| 0 <= i < rows ==> result.0[i].len() == cols && result.1[i].len() == cols,
        forall|i: int, j: int, k: int| 0 <= i < rows && 0 <= j < cols && 0 <= k < cols ==> 
            result.0[i][j] == result.0[i][k],
        forall|j: int, i: int, k: int| 0 <= j < cols && 0 <= i < rows && 0 <= k < rows ==> 
            result.1[i][j] == result.1[k][j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement mgrid using idx_to_coord with int casts */
    let mut rows_mat: Vec<Vec<f32>> = Vec::new();
    let mut cols_mat: Vec<Vec<f32>> = Vec::new();

    let mut i: usize = 0;
    while i < rows
        invariant i <= rows && rows_mat.len() == i
        decreases rows - i
    {
        let r_val: f32 = idx_to_coord(start_r, stop_r, rows as int, i as int);
        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < cols
            invariant j <= cols && row.len() == j
            decreases cols - j
        {
            row.push(r_val);
            j += 1;
        }
        rows_mat.push(row);
        i += 1;
    }

    let mut ii: usize = 0;
    while ii < rows
        invariant ii <= rows && cols_mat.len() == ii
        decreases rows - ii
    {
        let mut crow: Vec<f32> = Vec::new();
        let mut jj: usize = 0;
        while jj < cols
            invariant jj <= cols && crow.len() == jj
            decreases cols - jj
        {
            let c_val: f32 = idx_to_coord(start_c, stop_c, cols as int, jj as int);
            crow.push(c_val);
            jj += 1;
        }
        cols_mat.push(crow);
        ii += 1;
    }

    (rows_mat, cols_mat)
}
// </vc-code>

}
fn main() {}