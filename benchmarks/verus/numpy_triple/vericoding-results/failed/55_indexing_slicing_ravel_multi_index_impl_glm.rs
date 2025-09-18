// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fix type mismatch in linear_index by casting to usize */
spec fn linear_index(row: usize, col: usize, cols: usize) -> usize {
    (row * cols + col) as usize
}

proof fn linear_index_valid(row: usize, col: usize, rows: usize, cols: usize)
    requires row < rows && col < cols,
    ensures linear_index(row, col, cols) < rows * cols
{
    assert(linear_index(row, col, cols) <= (rows - 1) * cols + (cols - 1));
    assert((rows - 1) * cols + (cols - 1) == rows * cols - 1);
    assert(linear_index(row, col, cols) < rows * cols);
}
// </vc-helpers>

// <vc-spec>
fn ravel_multi_index(row_indices: &Vec<usize>, col_indices: &Vec<usize>, rows: usize, cols: usize) -> (result: Vec<usize>)
    requires 
        row_indices.len() == col_indices.len(),
        forall|i: int| 0 <= i < row_indices.len() ==> row_indices[i] < rows,
        forall|i: int| 0 <= i < col_indices.len() ==> col_indices[i] < cols,
    ensures 
        result.len() == row_indices.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == row_indices[i] * cols + col_indices[i] && 
            result[i] < rows * cols,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fix type annotation for result vector */
{
    let n = row_indices.len();
    let mut result: Vec<usize> = Vec::with_capacity(n);
    for i in 0..n
        invariant 
            0 <= i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> 
                result[k] == linear_index(row_indices[k], col_indices[k], cols) && 
                result[k] < rows * cols
    {
        let row = row_indices[i];
        let col = col_indices[i];
        let index = row * cols + col;
        proof {
            linear_index_valid(row, col, rows, cols);
            assert(index == linear_index(row, col, cols));
        }
        result.push(index);
    }
    result
}
// </vc-code>

}
fn main() {}