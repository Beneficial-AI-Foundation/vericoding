// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Use proper int-to-f32 casts with f32 functions */
#[verifier::spec]
fn row_val_spec(rows: usize, cols: usize, start_r: f32, stop_r: f32, i: usize) -> f32 {
    let step_r = if rows > 1 { (stop_r - start_r) / (f32_sub(rows, 1) as f32) } else { 0.0 };
    start_r + (i as f32) * step_r
}

#[verifier::spec]
fn col_val_spec(rows: usize, cols: usize, start_c: f32, stop_c: f32, j: usize) -> f32 {
    let step_c = if cols > 1 { (stop_c - start_c) / (f32_sub(cols, 1) as f32) } else { 0.0 };
    start_c + (j as f32) * step_c
}

#[verifier::spec]
fn f32_sub(a: usize, b: usize) -> f32 {
    (a - b) as f32
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
/* code modified by LLM (iteration 5): Replace direct int-to-f32 casts with helper function */
{
    let mut r_grid = Vec::<Vec<f32>>::new();
    let mut c_grid = Vec::<Vec<f32>>::new();
    
    let step_r = if rows > 1 { (stop_r - start_r) / ((rows - 1) as f32) } else { 0.0 };
    let step_c = if cols > 1 { (stop_c - start_c) / ((cols - 1) as f32) } else { 0.0 };
    
    let mut i: usize = 0;
    while i < rows
        invariant
            i <= rows,
            r_grid.len() == i,
            c_grid.len() == i,
            forall|k: int| 0 <= k < i ==> r_grid[k].len() == cols && c_grid[k].len() == cols,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < cols ==> r_grid[k][l] == row_val_spec(rows, cols, start_r, stop_r, k as usize),
            forall|k: int, l: int| 0 <= k < i && 0 <= l < cols ==> c_grid[k][l] == col_val_spec(rows, cols, start_c, stop_c, l as usize),
    {
        let mut r_row = Vec::<f32>::new();
        let mut c_row = Vec::<f32>::new();
        let mut j: usize = 0;
        
        while j < cols
            invariant
                j <= cols,
                r_row.len() == j,
                c_row.len() == j,
                forall|l: int| 0 <= l < j ==> r_row[l] == row_val_spec(rows, cols, start_r, stop_r, i),
                forall|l: int| 0 <= l < j ==> c_row[l] == col_val_spec(rows, cols, start_c, stop_c, l as usize),
        {
            r_row.push(row_val_spec(rows, cols, start_r, stop_r, i));
            c_row.push(col_val_spec(rows, cols, start_c, stop_c, j));
            j += 1;
        }
        
        r_grid.push(r_row);
        c_grid.push(c_row);
        i += 1;
    }
    
    (r_grid, c_grid)
}
// </vc-code>

}
fn main() {}