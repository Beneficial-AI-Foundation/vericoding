// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn half_f32(x: f32) -> f32;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide executable half_f32 for runtime use */
fn half_f32(x: f32) -> f32 {
    x / 2.0
}
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
    /* code modified by LLM (iteration 5): construct two-element vector with off and half of scl */
    let mut result: Vec<f32> = Vec::new();
    result.push(off);
    result.push(half_f32(scl));
    result
}
// </vc-code>


}
fn main() {}