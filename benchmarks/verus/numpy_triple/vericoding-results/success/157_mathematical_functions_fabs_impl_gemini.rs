// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): created a helper function for f32 absolute value, as f32::abs is not supported */
fn abs_f32(x: f32) -> (res: f32) {
    if x < 0.0 {
        -x
    } else {
        x
    }
}
// </vc-helpers>

// <vc-spec>
fn fabs(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): replaced unsupported f32::abs call with a custom helper function */
{
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
        decreases x.len() - i
    {
        result.push(abs_f32(x[i]));
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}