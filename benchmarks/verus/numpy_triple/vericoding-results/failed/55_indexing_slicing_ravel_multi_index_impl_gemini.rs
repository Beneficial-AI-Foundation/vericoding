// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed, helper is correct */
proof fn lemma_ravel_in_bounds(r_idx: usize, c_idx: usize, rows: usize, cols: usize)
    requires
        r_idx < rows,
        c_idx < cols,
    ensures
        r_idx * cols + c_idx < rows * cols,
{
    assert(r_idx * cols + c_idx < rows * cols) by(nonlinear_arith) {
        assert(r_idx < rows);
        assert(c_idx < cols);
    }
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
{
    /* code modified by LLM (iteration 5): fixed indexing type inside proof block from usize to int */
    let mut result: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < row_indices.len()
        invariant
            0 <= i <= row_indices.len(),
            row_indices.len() == col_indices.len(),
            result.len() == i,
            forall|k: int| 0 <= k < row_indices.len() ==> row_indices[k] < rows,
            forall|k: int| 0 <= k < col_indices.len() ==> col_indices[k] < cols,
            forall|j: int| 0 <= j < i ==> 
                (result[j] == row_indices[j] * cols + col_indices[j] && result[j] < rows * cols),
        decreases row_indices.len() - i
    {
        proof {
            lemma_ravel_in_bounds(row_indices[i as int], col_indices[i as int], rows, cols);
        }
        let raveled_index = row_indices[i] * cols + col_indices[i];
        result.push(raveled_index);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}