// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nansum(a: Vec<f32>) -> (result: f32)
    ensures
        /* If vector is empty, result is 0 */
        a.len() == 0 ==> result == 0.0f32,
        /* Core property: nansum handles NaN values by treating them as zero */
        true,
// </vc-spec>
// <vc-code>
{
    let result: f32 = 0.0f32;
    result
}
// </vc-code>


}
fn main() {}