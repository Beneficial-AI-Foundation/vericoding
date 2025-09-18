// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn loadtxt(filename: Seq<char>, delimiter: Seq<char>, skiprows: usize, rows: usize, cols: usize) -> (result: Vec<Vec<f64>>)
    requires 
        rows > 0,
        cols > 0,
        filename.len() > 0,
    ensures
        result.len() == rows,
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == cols,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut row_idx: usize = 0;
    
    while row_idx < rows
        invariant
            result.len() == row_idx,
            row_idx <= rows,
            forall|i: int| 0 <= i < result.len() ==> result@[i].len() == cols,
        decreases rows - row_idx
    {
        let mut col_vec: Vec<f64> = Vec::new();
        let mut col_idx: usize = 0;
        
        while col_idx < cols
            invariant
                col_vec.len() == col_idx,
                col_idx <= cols,
            decreases cols - col_idx
        {
            col_vec.push(0.0);
            col_idx = col_idx + 1;
        }
        
        result.push(col_vec);
        row_idx = row_idx + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}