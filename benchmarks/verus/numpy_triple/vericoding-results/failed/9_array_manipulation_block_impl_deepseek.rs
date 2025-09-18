// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn helper_lemma1(top_left: &Vec<Vec<f32>>, top_right: &Vec<Vec<f32>>, bottom_left: &Vec<Vec<f32>>, bottom_right: &Vec<Vec<f32>>) 
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
        forall|i: int| 0 <= i < bottom_right.len() ==> #[trigger] bottom_right[i].len() == bottom_right[0].len()
{
    assert(top_left.len() + bottom_left.len() > 0);
    assert(top_left[0].len() + top_right[0].len() > 0);
}

proof fn helper_lemma2(v: &Vec<Vec<f32>>, i: int, j: int) 
    requires 
        v.len() > 0,
        forall|k: int| 0 <= k < v.len() ==> #[trigger] v[k].len() == v[0].len(),
        0 <= i < v.len(),
        0 <= j < v[0].len()
{
    assert(0 <= j < v@[i].len());
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
/* code modified by LLM (iteration 5): Fix invariant syntax with proper curly braces */
{
    proof { helper_lemma1(&top_left, &top_right, &bottom_left, &bottom_right); }
    
    let total_rows = top_left.len() + bottom_left.len();
    let total_cols = top_left[0].len() + top_right[0].len();
    let mut result = Vec::<Vec<f32>>::new();
    
    let mut i = 0;
    while i < total_rows
        decreases total_rows - i
        invariant {
            i <= total_rows,
            result.len() == i,
            forall|k: int| 0 <= k < result.len() ==> #[trigger] result[k].len() == total_cols
        }
    {
        let mut row = Vec::<f32>::new();
        let mut j = 0;
        
        while j < total_cols
            decreases total_cols - j
            invariant {
                j <= total_cols,
                row.len() == j
            }
        {
            if i < top_left.len() {
                if j < top_left[0].len() {
                    let value = top_left[i][j];
                    row.push(value);
                } else {
                    let col = j - top_left[0].len();
                    proof { helper_lemma2(&top_right, i, col); }
                    let value = top_right[i][col];
                    row.push(value);
                }
            } else {
                let row_idx = i - top_left.len();
                if j < bottom_left[0].len() {
                    proof { helper_lemma2(&bottom_left, row_idx, j); }
                    let value = bottom_left[row_idx][j];
                    row.push(value);
                } else {
                    let col = j - bottom_left[0].len();
                    proof { helper_lemma2(&bottom_right, row_idx, col); }
                    let value = bottom_right[row_idx][col];
                    row.push(value);
                }
            }
            j += 1;
        }
        
        result.push(row);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}