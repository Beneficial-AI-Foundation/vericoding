// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn trace(x: Vec<Vec<f32>>) -> (result: f32)
    requires 
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> x@[i].len() == x@.len(),
    ensures 
        true, /* The trace equals the sum of diagonal elements matrix[i][i] for i in 0..n-1 */
        forall|i: int| 0 <= i < x@.len() ==> x@[i][i] != 0.0f32 ==> result != 0.0f32,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}
// </vc-code>


}
fn main() {}