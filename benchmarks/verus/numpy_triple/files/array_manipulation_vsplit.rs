// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn vsplit(mat: Vec<Vec<f32>>, k: usize) -> (result: Vec<Vec<Vec<f32>>>)
    requires 
        k > 0,
        mat.len() > 0,
        mat.len() % k == 0,
        forall|i: int| 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
    ensures
        result.len() == k,
        forall|split_idx: int| 0 <= split_idx < k ==> result[split_idx].len() == mat.len() / k,
        forall|split_idx: int, row_idx: int, col_idx: int| 
            0 <= split_idx < k && 0 <= row_idx < mat.len() / k && 0 <= col_idx < mat[0].len() ==>
            exists|global_row: int| 
                global_row == split_idx * (mat.len() / k) + row_idx &&
                0 <= global_row < mat.len() &&
                result[split_idx][row_idx][col_idx] == mat[global_row][col_idx],
        forall|orig_row: int| 0 <= orig_row < mat.len() ==>
            exists|split_idx: int, row_idx: int|
                0 <= split_idx < k && 0 <= row_idx < mat.len() / k &&
                orig_row == split_idx * (mat.len() / k) + row_idx,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}