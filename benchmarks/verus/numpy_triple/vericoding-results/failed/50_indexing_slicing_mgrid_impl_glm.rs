// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed parameter types from int to usize to use in executable code */
fn compute_row_value(rows: usize, i: usize, start_r: f32, stop_r: f32) -> f32
    requires i < rows,
{
    if rows == 1 {
        start_r
    } else {
        start_r + (stop_r - start_r) * (i as f32) / ((rows - 1) as f32)
    }
}

/* helper modified by LLM (iteration 5): changed parameter types from int to usize to use in executable code */
fn compute_col_value(cols: usize, j: usize, start_c: f32, stop_c: f32) -> f32
    requires j < cols,
{
    if cols == 1 {
        start_c
    } else {
        start_c + (stop_c - start_c) * (j as f32) / ((cols - 1) as f32)
    }
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
/* code modified by LLM (iteration 5): removed casts to int when calling helper functions */
{
    let mut row_matrix = Vec::new();
    for i in 0..rows {
        let val = compute_row_value(rows, i, start_r, stop_r);
        let mut row = Vec::new();
        for _ in 0..cols {
            row.push(val);
        }
        row_matrix.push(row);
    }

    let mut col_matrix = Vec::new();
    for i in 0..rows {
        let mut row = Vec::new();
        for j in 0..cols {
            let val = compute_col_value(cols, j, start_c, stop_c);
            row.push(val);
        }
        col_matrix.push(row);
    }

    (row_matrix, col_matrix)
}
// </vc-code>

}
fn main() {}