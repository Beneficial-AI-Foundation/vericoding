// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn mat_global_row(mat_len: int, k: int, split_idx: int, row_idx: int) -> int {
    split_idx * (mat_len / k) + row_idx
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
/* code modified by LLM (iteration 5): fixed compilation error by removing outer parentheses around the conjunction in the forall assert body */
/* code modified by LLM (iteration 4): implemented body with proof assertions to verify bounds, prevent arithmetic errors by using int types, and establish postconditions */
{
    proof {
        assert(forall|i: int| #![trigger mat[i]] 0 <= i < mat.len() ==> mat[i].len() == mat[0].len());
        assert(mat.len() > 0);
        assert(k > 0);
        assert(mat.len() % k == 0);
    }
    let rows_per_split: usize = mat.len() / k;
    let mut result: Vec<Vec<Vec<f32>>> = Vec::new();
    for split_idx in 0..k {
        let mut submat: Vec<Vec<f32>> = Vec::new();
        for row_idx in 0..rows_per_split {
            let global_row_int = split_idx as int * rows_per_split as int + row_idx as int;
            proof {
                assert(mat_global_row(mat.len() as int, k as int, split_idx as int, row_idx as int) == global_row_int);
                assert(0 <= global_row_int && global_row_int < mat.len() as int);
            }
            let global_row = global_row_int as usize;
            submat.push(mat[global_row].clone());
        }
        result.push(submat);
    }
    proof {
        assert(result.len() == k);
        assert(forall|split_idx: int| #![trigger result[split_idx]] 0 <= split_idx < k as int ==> split_idx as usize < result.len() && result[split_idx as usize].len() == rows_per_split);
        assert(forall|split_idx: int, row_idx: int, col_idx: int| #![trigger result[split_idx][row_idx][col_idx]]
            0 <= split_idx < k as int && 0 <= row_idx < rows_per_split as int && 0 <= col_idx < mat[0].len() as int ==>
            {
                let global_row_int = mat_global_row(mat.len() as int, k as int, split_idx, row_idx);
                0 <= global_row_int < mat.len() as int && result[split_idx][row_idx][col_idx] == mat[global_row_int as usize][col_idx as usize]
            });
        assert(forall|orig_row: int| #![trigger mat[orig_row]] 0 <= orig_row < mat.len() ==>
            exists|split_idx: int, row_idx: int|
                #![trigger (split_idx * rows_per_split as int + row_idx)]
                0 <= split_idx < k as int && 0 <= row_idx < rows_per_split as int &&
                orig_row == split_idx * rows_per_split as int + row_idx);
    }
    result
}
// </vc-code>

}
fn main() {}