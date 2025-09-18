// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected signature for tuple return. */
spec fn get_mat_dims(mat: Vec<Vec<f32>>) -> (rows: int, cols: int)
    requires
        mat.len() > 0,
        forall|i: int| #![trigger mat[i]] 0 <= i < mat.len() ==> mat[i].len() == mat[0].len(),
    ensures
        mat.len() == rows,
        mat[0].len() == cols,
{
    (mat.len() as int, mat[0].len() as int)
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
/* code modified by LLM (iteration 5): Initial implementation for vsplit based on the refined spec. */
{
    let (rows_int, cols_int) = get_mat_dims(mat);
    let rows = rows_int as usize;
    let cols = cols_int as usize;
    let rows_per_split = rows / k;

    let mut result: Vec<Vec<Vec<f32>>> = Vec::new();
    
    let mut split_idx: usize = 0;
    while split_idx < k
        invariant
            0 <= split_idx as int <= k as int,
            result.len() == split_idx,
            
            // result parts up to split_idx are valid
            forall|s_idx: int| 0 <= s_idx < split_idx ==> result[s_idx].len() == rows_per_split as int,
            
            // Each row in a split is fully populated
            forall|s_idx: int, r_idx: int| 0 <= s_idx < split_idx && 0 <= r_idx < rows_per_split as int ==> result[s_idx][r_idx].len() == cols as int,
            
            // Values match the original matrix
            forall|s_idx: int, r_idx: int, c_idx: int|
                0 <= s_idx < split_idx && 0 <= r_idx < rows_per_split as int && 0 <= c_idx < cols as int ==> 
                #[trigger] result[s_idx][r_idx][c_idx] == mat[(s_idx * rows_per_split as int + r_idx) as usize][c_idx as usize],

    {
        let mut current_split: Vec<Vec<f32>> = Vec::new();

        let mut row_in_split: usize = 0;
        while row_in_split < rows_per_split
            invariant
                0 <= row_in_split as int <= rows_per_split as int,
                current_split.len() == row_in_split,
                
                // Each row is fully populated
                forall|r_idx: int| 0 <= r_idx < row_in_split ==> current_split[r_idx].len() == cols as int,

                // Values match the original matrix
                forall|r_idx: int, c_idx: int|
                    0 <= r_idx < row_in_split && 0 <= c_idx < cols as int ==> 
                    #[trigger] current_split[r_idx][c_idx] == mat[(split_idx * rows_per_split + r_idx) as usize][c_idx as usize],

        {
            let global_row = split_idx * rows_per_split + row_in_split;
            current_split.push(mat[global_row].clone()); // Use .clone() as Vec<Vec<f32>> does not implement Copy
            row_in_split = row_in_split + 1;
        }
        result.push(current_split);
        split_idx = split_idx + 1;
    }
    result
}
// </vc-code>

}
fn main() {}