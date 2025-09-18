// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Replaced `f32` arithmetic directly with `as f32` casts for `usize` parameters, and ensured all calculations are performed with `f32` to avoid `Integer` trait errors. */
spec fn get_row_val(row: usize, rows: usize, start_r: f32, stop_r: f32) -> f32 {
    if equal(rows, 1) { start_r }
    else { start_r + ( (stop_r - start_r) * (row as f32) ) / ((rows - 1) as f32) }
}
spec fn get_col_val(col: usize, cols: usize, start_c: f32, stop_c: f32) -> f32 {
    if equal(cols, 1) { start_c }
    else { start_c + ( (stop_c - start_c) * (col as f32) ) / ((cols - 1) as f32) }
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
/* code modified by LLM (iteration 5): Updated the invariants for `grid_c` to correctly reflect the values being stored based on `get_col_val` and added explicit `as int` casts for sequence indexing to satisfy Verus requirements. */
{
    let mut grid_r: Vec<Vec<f32>> = Vec::new();
    let mut grid_c: Vec<Vec<f32>> = Vec::new();

    let mut i: usize = 0;
    while i < rows
        invariant
            0 <= i && i <= rows,
            grid_r.len() == i,
            grid_c.len() == i,
            forall|idx: int| 0 <= idx < i ==> grid_r[idx].len() == cols && grid_c[idx].len() == cols,
            forall|idx_i: int, idx_j: int, idx_k: int|
                0 <= idx_i < i && 0 <= idx_j < cols && 0 <= idx_k < cols
                ==>
                grid_r[idx_i][idx_j] == grid_r[idx_i][idx_k],
            forall|idx_j: int, idx_i: int, idx_k: int|
                0 <= idx_j < cols && 0 <= idx_i < i && 0 <= idx_k < i // not idx_k < rows because idx_k and idx_i both represent iterating rows
                ==>
                grid_c[idx_i][idx_j] == get_col_val(idx_j as usize, cols, start_c, stop_c),
            forall|idx_i: int, idx_j: int| 0 <= idx_i < i && 0 <= idx_j < cols ==> grid_r[idx_i][idx_j] == get_row_val(idx_i as usize, rows, start_r, stop_r)
    {
        let mut row_r: Vec<f32> = Vec::new();
        let mut row_c: Vec<f32> = Vec::new();

        let mut j: usize = 0;
        while j < cols
            invariant
                0 <= j && j <= cols,
                row_r.len() == j,
                row_c.len() == j,
                forall|idx: int| 0 <= idx < j ==> row_r[idx] == get_row_val(i, rows, start_r, stop_r),
                forall|idx: int| 0 <= idx < j ==> row_c[idx] == get_col_val(idx as usize, cols, start_c, stop_c)
        {
            row_r.push(get_row_val(i, rows, start_r, stop_r));
            row_c.push(get_col_val(j, cols, start_c, stop_c));
            j = j + 1;
        }
        grid_r.push(row_r);
        grid_c.push(row_c);
        i = i + 1;
    }

    (grid_r, grid_c)
}
// </vc-code>

}
fn main() {}