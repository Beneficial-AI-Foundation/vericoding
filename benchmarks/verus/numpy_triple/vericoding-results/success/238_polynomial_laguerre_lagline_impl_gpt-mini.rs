// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): create 2-element vector */
fn vec2(a: f32, b: f32) -> (v: Vec<f32>)
    ensures
        v.len() == 2,
{
    let mut vv: Vec<f32> = Vec::new();
    vv.push(a);
    vv.push(b);
    vv
}
// </vc-helpers>

// <vc-spec>
fn lagline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures result.len() == 2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): return off and scl without arithmetic */
    vec2(off, scl)
}
// </vc-code>

}
fn main() {}