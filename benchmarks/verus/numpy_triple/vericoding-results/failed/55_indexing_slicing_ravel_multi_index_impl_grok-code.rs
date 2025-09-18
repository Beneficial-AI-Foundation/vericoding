// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 2): Fixed compilation errors by using Vec indexing and loop to build result vector with invariants. */
    let mut result: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < row_indices.len()
        invariant 
            0 <= i <= row_indices.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == row_indices[j] * cols + col_indices[j]
        decreases (row_indices.len() - i)
    {
        result.push(row_indices[i] * cols + col_indices[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}