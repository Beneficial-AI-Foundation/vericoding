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
        forall|i: int| 0 <= i < top_left.len() ==> top_left[i].len() == top_left[0].len(),
        forall|i: int| 0 <= i < top_right.len() ==> top_right[i].len() == top_right[0].len(),
        forall|i: int| 0 <= i < bottom_left.len() ==> bottom_left[i].len() == bottom_left[0].len(),
        forall|i: int| 0 <= i < bottom_right.len() ==> bottom_right[i].len() == bottom_right[0].len(),
    ensures
        result.len() == top_left.len() + bottom_left.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == top_left[0].len() + top_right[0].len(),

        forall|i: int, j: int| 
            0 <= i < top_left.len() && 0 <= j < top_left[0].len() ==> 
            result[i][j] == top_left[i][j],

        forall|i: int, j: int|
            0 <= i < top_right.len() && 0 <= j < top_right[0].len() ==>
            result[i][top_left[0].len() + j] == top_right[i][j],

        forall|i: int, j: int|
            0 <= i < bottom_left.len() && 0 <= j < bottom_left[0].len() ==>
            result[top_left.len() + i][j] == bottom_left[i][j],

        forall|i: int, j: int|
            0 <= i < bottom_right.len() && 0 <= j < bottom_right[0].len() ==>
            result[top_left.len() + i][top_left[0].len() + j] == bottom_right[i][j],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}