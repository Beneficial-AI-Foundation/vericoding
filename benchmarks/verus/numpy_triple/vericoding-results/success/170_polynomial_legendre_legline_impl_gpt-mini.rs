// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): construct a Vec with two f32 elements */
fn make_vec2(a: f32, b: f32) -> Vec<f32> { let mut v: Vec<f32> = Vec::new(); v.push(a); v.push(b); v }
// </vc-helpers>

// <vc-spec>
fn legline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures
        result.len() == 2,
        result[0] == off,
        result[1] == scl
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): build Vec without using view() */
    let mut v: Vec<f32> = Vec::new();
    v.push(off);
    v.push(scl);
    v
}
// </vc-code>

}
fn main() {}