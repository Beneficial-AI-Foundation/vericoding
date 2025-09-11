// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn bmat(top_left: Vec<f32>, top_right: Vec<f32>, bottom_left: Vec<f32>, bottom_right: Vec<f32>) -> (result: Vec<f32>)
    requires 
        top_left.len() == top_right.len(),
        top_left.len() == bottom_left.len(),
        top_left.len() == bottom_right.len(),
    ensures
        result.len() == 4 * top_left.len(),
        forall|i: int| 0 <= i < top_left.len() ==> result[i] == top_left[i],
        forall|i: int| 0 <= i < top_right.len() ==> result[i + top_left.len()] == top_right[i],
        forall|i: int| 0 <= i < bottom_left.len() ==> result[i + 2 * top_left.len()] == bottom_left[i],
        forall|i: int| 0 <= i < bottom_right.len() ==> result[i + 3 * top_left.len()] == bottom_right[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}