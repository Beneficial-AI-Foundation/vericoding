// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert usize to f32 using Verus integer arithmetic */
fn linspace(start: f32, stop: f32, num: usize) -> (result: Vec<f32>)
    requires num > 0,
    ensures result.len() == num,
{
    let mut result = Vec::new();
    let step = if num == 1 { 0.0 } else { (stop - start) / (num - 1) as f32 };
    let mut i = 0;
    while i < num
        invariant
            0 <= i <= num,
            result.len() == i,
    {
        let value = start + step * (i as f32);
        result.push(value);
        i += 1;
    }
    result
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
    /* code modified by LLM (iteration 5): using corrected linspace helper without nested casts */
    let row_values = linspace(start_r, stop_r, rows);
    let col_values = linspace(start_c, stop_c, cols);
    
    let mut row_matrix: Vec<Vec<f32>> = Vec::new();
    let mut col_matrix: Vec<Vec<f32>> = Vec::new();
    
    let mut i = 0;
    while i < rows
        invariant
            0 <= i <= rows,
            row_matrix.len() == i,
            col_matrix.len() == i,
            forall|k: int| 0 <= k < i ==> row_matrix[k].len() == cols && col_matrix[k].len() == cols,
    {
        let mut row_vec: Vec<f32> = Vec::new();
        let mut col_vec: Vec<f32> = Vec::new();
        
        let mut j = 0;
        while j < cols
            invariant
                0 <= j <= cols,
                row_vec.len() == j,
                col_vec.len() == j,
        {
            row_vec.push(row_values[i]);
            col_vec.push(col_values[j]);
            j += 1;
        }
        
        row_matrix.push(row_vec);
        col_matrix.push(col_vec);
        i += 1;
    }
    
    (row_matrix, col_matrix)
}
// </vc-code>

}
fn main() {}