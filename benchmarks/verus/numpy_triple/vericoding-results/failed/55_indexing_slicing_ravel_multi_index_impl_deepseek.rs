// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Convert usize to int for verification */
fn ravel_index(row: int, col: int, cols: int) -> (result: int)
    requires
        row * cols + col >= 0,
        row >= 0,
        col >= 0,
        cols > 0
    ensures
        result == row * cols + col
{
    row * cols + col
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
/* code modified by LLM (iteration 5): Fixed type mismatches by converting usize to int for verification */
{
    let len = row_indices.len() as int;
    let mut result_vec: Vec<usize> = Vec::new();
    let mut i: int = 0;
    while i < len
        invariant
            0 <= i <= len,
            result_vec.len() == i as usize,
            forall|j: int| 0 <= j < i ==> (
                0 <= j < row_indices@.len() && 0 <= j < col_indices@.len()
            ),
            forall|j: int| 0 <= j < i ==> 
                result_vec@[j as usize] == (row_indices@[j as usize] as int * cols as int + col_indices@[j as usize] as int) as usize,
            forall|j: int| 0 <= j < i ==> result_vec@[j as usize] < rows * cols
        decreases len - i
    {
        assert(0 <= i < row_indices@.len());
        assert(0 <= i < col_indices@.len());
        assert(row_indices@[i as usize] < rows);
        assert(col_indices@[i as usize] < cols);
        let idx_val = ravel_index(row_indices@[i as usize] as int, col_indices@[i as usize] as int, cols as int);
        proof {
            assert(row_indices@[i as usize] * cols + col_indices@[i as usize] == idx_val);
        }
        result_vec.push(idx_val as usize);
        i += 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}