// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed type issues by removing nat casts and sequence views, accessing Vecs directly with usize indices */
    let row_top = top_left.len();
    let col_left = top_left[0].len();
    let row_bottom = bottom_left.len();
    let col_right = top_right[0].len();
    let row_len = col_left + col_right;
    let total_rows = row_top + row_bottom;
    let mut result: Vec<Vec<f32>> = Vec::with_capacity(total_rows);
    for i in 0..row_top {
        let mut row: Vec<f32> = Vec::with_capacity(row_len);
        for j in 0..col_left {
            row.push(top_left[i][j]);
        }
        for j in 0..col_right {
            row.push(top_right[i][j]);
        }
        result.push(row);
    }
    for i in 0..row_bottom {
        let mut row: Vec<f32> = Vec::with_capacity(row_len);
        for j in 0..col_left {
            row.push(bottom_left[i][j]);
        }
        for j in 0..col_right {
            row.push(bottom_right[i][j]);
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}