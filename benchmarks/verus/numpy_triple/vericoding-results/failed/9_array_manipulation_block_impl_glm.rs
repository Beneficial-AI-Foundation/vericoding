// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added helper function to safely get vector length */
spec fn get_len<T>(v: &Vec<T>) -> nat
    recommends
        v@.len() == v.len(),
{
    v@.len()
}
// </vc-helpers>

// <vc-spec>
fn block(
    top_left: Vec<Vec<f32>>,
    top_right: Vec<Vec<f32>>,
    bottom_left: Vec<Vec<f32>>,
    bottom_right: Vec<Vec<f32>>
) -> (result: Vec<Vec<f32>>)
    requires
        top_left.len() > 0,
        top_right.len() > 0,
        bottom_left.len() > 0,
        bottom_right.len() > 0,
        top_left.len() == top_right.len(),
        bottom_left.len() == bottom_right.len(),
        top_left[0].len() == bottom_left[0].len(),
        top_right[0].len() == bottom_right[0].len(),
        forall|i: int| 0 <= i < top_left.len() ==> #[trigger] top_left[i].len() == top_left[0].len(),
        forall|i: int| 0 <= i < top_right.len() ==> #[trigger] top_right[i].len() == top_right[0].len(),
        forall|i: int| 0 <= i < bottom_left.len() ==> #[trigger] bottom_left[i].len() == bottom_left[0].len(),
        forall|i: int| 0 <= i < bottom_right.len() ==> #[trigger] bottom_right[i].len() == bottom_right[0].len(),
    ensures
        result.len() == top_left.len() + bottom_left.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == top_left[0].len() + top_right[0].len(),

        forall|i: int, j: int| 
            0 <= i < top_left.len() && 0 <= j < top_left[0].len() ==> 
            #[trigger] result[i][j] == top_left[i][j],

        forall|i: int, j: int|
            0 <= i < top_right.len() && 0 <= j < top_right[0].len() ==>
            #[trigger] result[i][top_left[0].len() + j] == top_right[i][j],

        forall|i: int, j: int|
            0 <= i < bottom_left.len() && 0 <= j < bottom_left[0].len() ==>
            #[trigger] result[top_left.len() + i][j] == bottom_left[i][j],

        forall|i: int, j: int|
            0 <= i < bottom_right.len() && 0 <= j < bottom_right[0].len() ==>
            #[trigger] result[top_left.len() + i][top_left[0].len() + j] == bottom_right[i][j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed iterator issues by storing lengths in variables and added proper invariants */
    let mut result: Vec<Vec<f32>> = Vec::new();
    
    let top_left_len = top_left.len();
    let top_right_len = top_right.len();
    let bottom_left_len = bottom_left.len();
    let bottom_right_len = bottom_right.len();
    
    let top_left_col_len = top_left[0].len();
    let top_right_col_len = top_right[0].len();
    let bottom_left_col_len = bottom_left[0].len();
    let bottom_right_col_len = bottom_right[0].len();
    
    // Build the top part: for each row in top_left and top_right
    for i in 0..top_left_len
        invariant result.len() == i,
        invariant forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == top_left_col_len + top_right_col_len,
    {
        let mut new_row: Vec<f32> = Vec::new();
        // Append top_left[i]
        for j in 0..top_left_col_len
            invariant new_row.len() == j,
        {
            new_row.push(top_left[i][j]);
        }
        // Append top_right[i]
        for j in 0..top_right_col_len
            invariant new_row.len() == top_left_col_len + j,
        {
            new_row.push(top_right[i][j]);
        }
        result.push(new_row);
    }

    // Build the bottom part: for each row in bottom_left and bottom_right
    for i in 0..bottom_left_len
        invariant result.len() == top_left_len + i,
        invariant forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].len() == top_left_col_len + top_right_col_len,
    {
        let mut new_row: Vec<f32> = Vec::new();
        // Append bottom_left[i]
        for j in 0..bottom_left_col_len
            invariant new_row.len() == j,
        {
            new_row.push(bottom_left[i][j]);
        }
        // Append bottom_right[i]
        for j in 0..bottom_right_col_len
            invariant new_row.len() == bottom_left_col_len + j,
        {
            new_row.push(bottom_right[i][j]);
        }
        result.push(new_row);
    }

    result
}
// </vc-code>

}
fn main() {}