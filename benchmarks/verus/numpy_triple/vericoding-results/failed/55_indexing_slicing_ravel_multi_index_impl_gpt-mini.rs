// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute 2D index from row,col */
fn compute_index(r: usize, c: usize, cols: usize) -> usize { r * cols + c }
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
    /* code modified by LLM (iteration 5): build result by computing r*cols+c for each index */
    let n: usize = row_indices.len();
    let mut result = Vec::<usize>::new();
    let mut i: usize = 0;
    while i < n
        invariant result.len() == i;
        invariant forall|j: int| 0 <= j && j < i as int ==> result@[j] == row_indices@[j] * cols + col_indices@[j];
        decreases n - i;
    {
        let r: usize = row_indices[i];
        let c: usize = col_indices[i];
        let idx: usize = compute_index(r, c, cols);
        result.push(idx);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}