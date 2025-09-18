// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma syntax by removing 'fn' keyword */
spec fn valid_indices(arrays: &Vec<Vec<f32>>, i: int, j: int) -> bool {
    0 <= i < arrays[0].len() && 0 <= j < arrays.len()
}

proof fn length_preservation(arrays: &Vec<Vec<f32>>, result: &Vec<f32>)
    requires
        arrays.len() > 0,
        forall|k: int| 0 <= k < arrays.len() ==> arrays[k].len() == arrays[0].len(),
        result.len() == arrays.len() * arrays[0].len(),
    ensures
        forall|i: int, j: int| valid_indices(arrays, i, j) ==> 0 <= j * arrays[0].len() + i < result.len(),
{
}
// </vc-helpers>

// <vc-spec>
fn column_stack(arrays: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires
        arrays.len() > 0,
        forall|i: int| 0 <= i < arrays.len() ==> #[trigger] arrays[i].len() == arrays[0].len(),
    ensures
        result.len() == arrays.len() * arrays[0].len(),
        forall|i: int, j: int| 
            0 <= i < arrays[0].len() && 0 <= j < arrays.len() ==>
            #[trigger] result[j * arrays[0].len() + i] == arrays[j][i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type casting for indices */
    let mut result = Vec::new();
    let inner_len = arrays[0].len();
    let outer_len = arrays.len();
    
    for j in 0..outer_len
        invariant
            result.len() == j * inner_len,
            forall|row_idx: int| 0 <= row_idx < j ==> 
                forall|col_idx: int| 0 <= col_idx < inner_len ==> 
                    result[row_idx * inner_len + col_idx] == arrays[row_idx as int][col_idx as int],
    {
        for i in 0..inner_len
            invariant
                result.len() == j * inner_len + i,
                forall|row_idx: int| 0 <= row_idx < j ==> 
                    forall|col_idx: int| 0 <= col_idx < inner_len ==> 
                        result[row_idx * inner_len + col_idx] == arrays[row_idx as int][col_idx as int],
                forall|col_idx: int| 0 <= col_idx < i ==> 
                    result[j * inner_len + col_idx] == arrays[j as int][col_idx as int],
        {
            result.push(arrays[j][i]);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}