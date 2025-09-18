// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove unsupported f32 to f64 casts by performing all calculations in f32 */
fn compute_step(start: f32, stop: f32, steps: usize) -> f32 {
    if steps == 1 { 0.0 } else { (stop - start) / ((steps - 1) as f32) }
}

fn get_row_val(row_idx: usize, start_r: f32, stop_r: f32, rows: usize) -> f32 {
    start_r + (row_idx as f32) * compute_step(start_r, stop_r, rows)
}

fn get_col_val(col_idx: usize, start_c: f32, stop_c: f32, cols: usize) -> f32 {
    start_c + (col_idx as f32) * compute_step(start_c, stop_c, cols)
}
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
/* code modified by LLM (iteration 5): implement mgrid with while loops using corrected helper functions */
    let mut x: Matrix = Vec::new();
    let mut y: Matrix = Vec::new();
    let mut i = 0;
    while i < rows 
        invariant 
            x.len() == i,
            forall |k| #![trigger x[k]] 0 <= k < i ==> x[k].len() == cols,
            forall |k, j, l| #![trigger x[k][j]] 0 <= k < i && 0 <= j < l < cols ==> x[k][j] == x[k][l],
    {
        let rv = get_row_val(i, start_r, stop_r, rows);
        let row_x = vec![rv; cols];
        x.push(row_x);
        i += 1;
    }
    let mut i = 0;
    while i < rows 
        invariant 
            y.len() == i,
            forall |k| #![trigger y[k]] 0 <= k < i ==> y[k].len() == cols,
            forall |k, l, j| #![trigger y[k][j]] 0 <= k < l < rows && 0 <= j < cols ==> y[k][j] == y[l][j],
    {
        let mut row_y = Vec::new();
        let mut j = 0;
        while j < cols 
            invariant 
                row_y.len() == j,
        {
            let cv = get_col_val(j, start_c, stop_c, cols);
            row_y.push(cv);
            j += 1;
        }
        y.push(row_y);
        i += 1;
    }
    (x, y)
}
// </vc-code>

}
fn main() {}