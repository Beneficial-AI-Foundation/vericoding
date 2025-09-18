// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unused helper and added proper invariant syntax fix */
proof fn empty_helper() {
    // No helper needed for this implementation
}
// </vc-helpers>

// <vc-spec>
fn vsplit(mat: Vec<Vec<f32>>, k: usize) -> (result: Vec<Vec<Vec<f32>>>)
    requires 
        k > 0,
        mat.len() > 0,
        mat.len() % k == 0,
        forall|i: int| #![trigger mat[i]] 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
    ensures
        result.len() == k,
        forall|split_idx: int| #![trigger result[split_idx]] 0 <= split_idx < k ==> result[split_idx].len() == mat.len() / k,
        forall|split_idx: int, row_idx: int, col_idx: int| #![trigger result[split_idx][row_idx][col_idx]]
            0 <= split_idx < k && 0 <= row_idx < mat.len() / k && 0 <= col_idx < mat[0].len() ==>
            exists|global_row: int| 
                global_row == split_idx * (mat.len() / k) + row_idx &&
                0 <= global_row < mat.len() &&
                result[split_idx][row_idx][col_idx] == #[trigger] mat[global_row][col_idx],
        forall|orig_row: int| #![trigger mat[orig_row]] 0 <= orig_row < mat.len() ==>
            exists|split_idx: int, row_idx: int|
                0 <= split_idx < k && 0 <= row_idx < mat.len() / k &&
                orig_row == #[trigger] (split_idx * (mat.len() / k) + row_idx),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed invariant syntax with proper braces */
{
    let total_rows = mat.len();
    let rows_per_split = total_rows / k;
    let mut result: Vec<Vec<Vec<f32>>> = Vec::with_capacity(k);
    let mut i = 0;
    while i < k
        invariant
            i <= k,
            result.len() == i,
            forall|split_idx: int| 0 <= split_idx < i ==> result[split_idx].len() == rows_per_split,
            forall|split_idx: int, row_idx: int, col_idx: int| 
                0 <= split_idx < i && 0 <= row_idx < rows_per_split && 0 <= col_idx < mat[0].len() ==>
                result[split_idx][row_idx][col_idx] == mat[split_idx * rows_per_split + row_idx][col_idx]
    {
        let mut split_mat: Vec<Vec<f32>> = Vec::with_capacity(rows_per_split);
        let mut j = 0;
        while j < rows_per_split
            invariant
                j <= rows_per_split,
                split_mat.len() == j,
                forall|row_idx: int| 0 <= row_idx < j ==> split_mat[row_idx].len() == mat[0].len(),
                forall|row_idx: int, col_idx: int| 
                    0 <= row_idx < j && 0 <= col_idx < mat[0].len() ==>
                    split_mat[row_idx][col_idx] == mat[i * rows_per_split + row_idx][col_idx]
        {
            let global_row = i * rows_per_split + j;
            split_mat.push(mat[global_row].clone());
            j += 1;
        }
        result.push(split_mat);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}