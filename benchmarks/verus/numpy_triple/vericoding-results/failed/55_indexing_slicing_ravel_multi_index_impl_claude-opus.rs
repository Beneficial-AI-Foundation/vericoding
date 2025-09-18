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
    /* code modified by LLM (iteration 5): fixed type mismatch errors by using @[i] for sequence access */
    let mut result: Vec<usize> = Vec::new();
    let n = row_indices.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == row_indices.len(),
            n == col_indices.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == row_indices[j] * cols + col_indices[j],
            forall|j: int| 0 <= j < i ==> result[j] < rows * cols,
            forall|j: int| 0 <= j < row_indices.len() ==> row_indices[j] < rows,
            forall|j: int| 0 <= j < col_indices.len() ==> col_indices[j] < cols,
        decreases n - i
    {
        assert(row_indices@[i as int] < rows);
        assert(col_indices@[i as int] < cols);
        assert(row_indices@[i as int] * cols <= (rows - 1) * cols);
        assert((rows - 1) * cols + col_indices@[i as int] < rows * cols);
        assert(row_indices@[i as int] * cols + col_indices@[i as int] <= (rows - 1) * cols + col_indices@[i as int]);
        assert(row_indices@[i as int] * cols + col_indices@[i as int] < rows * cols);
        let flat_index = row_indices[i] * cols + col_indices[i];
        result.push(flat_index);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}