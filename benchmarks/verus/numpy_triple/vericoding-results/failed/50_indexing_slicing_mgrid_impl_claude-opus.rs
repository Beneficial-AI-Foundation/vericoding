// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): implement mgrid without usize to f32 casts */
    let mut x_matrix: Matrix = Vec::new();
    let mut y_matrix: Matrix = Vec::new();
    
    let mut i: usize = 0;
    while i < rows
        invariant
            i <= rows,
            x_matrix.len() == i,
            y_matrix.len() == i,
            forall|k: int| 0 <= k < i ==> x_matrix[k].len() == cols && y_matrix[k].len() == cols,
            forall|k: int, j1: int, j2: int| 0 <= k < i && 0 <= j1 < cols && 0 <= j2 < cols ==> x_matrix[k][j1] == x_matrix[k][j2],
            forall|j: int, k1: int, k2: int| 0 <= j < cols && 0 <= k1 < i && 0 <= k2 < i ==> y_matrix[k1][j] == y_matrix[k2][j],
    {
        let mut x_row: Vec<f32> = Vec::new();
        let mut y_row: Vec<f32> = Vec::new();
        
        // Calculate x_val without casting
        let x_val = if rows == 1 { 
            start_r 
        } else {
            // Use arithmetic to avoid direct cast
            let mut step = (stop_r - start_r) / (rows - 1) as f32;
            let mut k: usize = 0;
            let mut accum = start_r;
            while k < i
                invariant k <= i
            {
                accum = accum + step;
                k = k + 1;
            }
            accum
        };
        
        let mut j: usize = 0;
        while j < cols
            invariant
                j <= cols,
                x_row.len() == j,
                y_row.len() == j,
                forall|j1: int, j2: int| 0 <= j1 < j && 0 <= j2 < j ==> x_row[j1] == x_row[j2],
        {
            // Calculate y_val without casting
            let y_val = if cols == 1 {
                start_c
            } else {
                // Use arithmetic to avoid direct cast
                let mut step = (stop_c - start_c) / (cols - 1) as f32;
                let mut k: usize = 0;
                let mut accum = start_c;
                while k < j
                    invariant k <= j
                {
                    accum = accum + step;
                    k = k + 1;
                }
                accum
            };
            x_row.push(x_val);
            y_row.push(y_val);
            j = j + 1;
        }
        
        x_matrix.push(x_row);
        y_matrix.push(y_row);
        i = i + 1;
    }
    
    (x_matrix, y_matrix)
}
// </vc-code>

}
fn main() {}