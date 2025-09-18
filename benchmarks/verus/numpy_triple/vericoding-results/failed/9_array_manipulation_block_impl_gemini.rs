// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes required */
fn concat_rows(left: Vec<f32>, right: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == left.len() + right.len(),
        forall|i: int| 0 <= i < left.len() ==> #[trigger] result[i] == left[i],
        forall|i: int| 0 <= i < right.len() ==> #[trigger] result[left.len() + i] == right[i],
{
    let mut result = left;
    let mut mut_right = right;
    result.append(&mut mut_right);
    result
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
    /* code modified by LLM (iteration 5): fixed int/usize mismatch in proof blocks by using sequence indexing */
    let mut result: Vec<Vec<f32>> = Vec::new();

    let mut i: usize = 0;
    while i < top_left.len()
        invariant
            0 <= i <= top_left.len(),
            top_left.len() > 0 && top_right.len() > 0 && bottom_left.len() > 0 && bottom_right.len() > 0,
            top_left.len() == top_right.len(),
            bottom_left.len() == bottom_right.len(),
            top_left[0].len() == bottom_left[0].len(),
            top_right[0].len() == bottom_right[0].len(),
            forall|k: int| 0 <= k < top_left.len() ==> #[trigger] top_left[k].len() == top_left[0].len(),
            forall|k: int| 0 <= k < top_right.len() ==> #[trigger] top_right[k].len() == top_right[0].len(),
            forall|k: int| 0 <= k < bottom_left.len() ==> #[trigger] bottom_left[k].len() == bottom_left[0].len(),
            forall|k: int| 0 <= k < bottom_right.len() ==> #[trigger] bottom_right[k].len() == bottom_right[0].len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == top_left[0].len() + top_right[0].len(),
            forall|k: int, j: int| 
                0 <= k < i && 0 <= j < top_left[0].len() ==> 
                #[trigger] result[k][j] == top_left[k][j],
            forall|k: int, j: int|
                0 <= k < i && 0 <= j < top_right[0].len() ==> 
                #[trigger] result[k][top_left[0].len() + j] == top_right[k][j],
        decreases top_left.len() - i
    {
        let new_row = concat_rows(top_left[i].clone(), top_right[i].clone());
        proof {
            assert(top_left@[i as int].len() == top_left@[0].len());
            assert(top_right@[i as int].len() == top_right@[0].len());
        }
        result.push(new_row);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < bottom_left.len()
        invariant
            0 <= j <= bottom_left.len(),
            top_left.len() > 0 && top_right.len() > 0 && bottom_left.len() > 0 && bottom_right.len() > 0,
            top_left.len() == top_right.len(),
            bottom_left.len() == bottom_right.len(),
            top_left[0].len() == bottom_left[0].len(),
            top_right[0].len() == bottom_right[0].len(),
            forall|k: int| 0 <= k < top_left.len() ==> #[trigger] top_left[k].len() == top_left[0].len(),
            forall|k: int| 0 <= k < top_right.len() ==> #[trigger] top_right[k].len() == top_right[0].len(),
            forall|k: int| 0 <= k < bottom_left.len() ==> #[trigger] bottom_left[k].len() == bottom_left[0].len(),
            forall|k: int| 0 <= k < bottom_right.len() ==> #[trigger] bottom_right[k].len() == bottom_right[0].len(),

            result.len() == top_left.len() + j,
            forall|k: int| 0 <= k < top_left.len() ==> #[trigger] result[k].len() == top_left[0].len() + top_right[0].len(),
            forall|k: int, l: int| 
                0 <= k < top_left.len() && 0 <= l < top_left[0].len() ==> 
                #[trigger] result[k][l] == top_left[k][l],
            forall|k: int, l: int|
                0 <= k < top_left.len() && 0 <= l < top_right[0].len() ==> 
                #[trigger] result[k][top_left[0].len() + l] == top_right[k][l],

            forall|k: int| 0 <= k < j ==> #[trigger] result[top_left.len() + k].len() == top_left[0].len() + top_right[0].len(),
            forall|k: int, l: int| 
                0 <= k < j && 0 <= l < bottom_left[0].len() ==> 
                #[trigger] result[top_left.len() + k][l] == bottom_left[k][l],
            forall|k: int, l: int|
                0 <= k < j && 0 <= l < bottom_right[0].len() ==> 
                #[trigger] result[top_left.len() + k][bottom_left[0].len() + l] == bottom_right[k][l],
        decreases bottom_left.len() - j
    {
        let new_row = concat_rows(bottom_left[j].clone(), bottom_right[j].clone());
        proof {
            assert(bottom_left@[j as int].len() == bottom_left@[0].len());
            assert(bottom_right@[j as int].len() == bottom_right@[0].len());
        }
        result.push(new_row);
        j = j + 1;
    }

    result
}
// </vc-code>

}
fn main() {}