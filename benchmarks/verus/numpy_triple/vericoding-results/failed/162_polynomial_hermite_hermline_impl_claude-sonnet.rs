// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn half_f32(x: f32) -> f32;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix syntax for uninterpreted function declaration */
spec fn half_f32(x: f32) -> f32;
// </vc-helpers>

// <vc-spec>
fn hermline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures
        result.len() == 2,
        result[0] == off,
        result[1] == half_f32(scl)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simple implementation creating Vec with off and scl/2 */
    let mut result = Vec::new();
    result.push(off);
    result.push(scl / 2.0);
    result
}
// </vc-code>


}
fn main() {}