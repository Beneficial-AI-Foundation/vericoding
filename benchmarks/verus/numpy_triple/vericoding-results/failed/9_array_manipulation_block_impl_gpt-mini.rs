// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): total columns helper */
spec fn total_cols(left: Vec<Vec<f32>>, right: Vec<Vec<f32>>) -> int { left[0].len() + right[0].len() }
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
    /* code modified by LLM (iteration 5): assemble block matrix with row-wise pushes and proper invariants */
    let m_top = top_left.len();
    let m_bottom = bottom_left.len();
    let cols_l = top_left[0].len();
    let cols_r = top_right[0].len();
    let total_rows = m_top + m_bottom;
    let total_cols = cols_l + cols_r;

    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: int = 0;
    while i < total_rows
        invariant 0 <= i && i <= total_rows;
        invariant result.len() == i;
        invariant forall|k: int, j_: int| 0 <= k < i && 0 <= j_ < total_cols ==>
            (if k < m_top {
                if j_ < cols_l { result[k][j_] == top_left[k][j_] } else { result[k][j_] == top_right[k][j_ - cols_l] }
            } else {
                if j_ < cols_l { result[k][j_] == bottom_left[k - m_top][j_] } else { result[k][j_] == bottom_right[k - m_top][j_ - cols_l] }
            });
        decreases total_rows - i;
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: int = 0;
        if i < m_top {
            while j < total_cols
                invariant 0 <= j && j <= total_cols;
                invariant row.len() == j;
                decreases total_cols - j;
            {
                if j < cols_l {
                    row.push(top_left[i][j]);
                } else {
                    row.push(top_right[i][j - cols_l]);
                }
                j += 1;
            }
        } else {
            let bi = i - m_top;
            while j < total_cols
                invariant 0 <= j && j <= total_cols;
                invariant row.len() == j;
                decreases total_cols - j;
            {
                if j < cols_l {
                    row.push(bottom_left[bi][j]);
                } else {
                    row.push(bottom_right[bi][j - cols_l]);
                }
                j += 1;
            }
        }
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}