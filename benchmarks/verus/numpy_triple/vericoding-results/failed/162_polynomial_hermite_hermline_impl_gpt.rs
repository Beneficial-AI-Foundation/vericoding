// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn half_f32(x: f32) -> f32;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide a small exec helper to build a 2-element vector */
fn build_pair(a: f32, b: f32) -> (result: Vec<f32>)
    ensures
        result.len() == 2,
        result[0] == a,
        result[1] == b,
{
    let mut v: Vec<f32> = Vec::new();
    v.push(a);
    v.push(b);
    v
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
    /* code modified by LLM (iteration 2): construct the vector using helper and numeric half */
    let h: f32 = scl / 2.0f32;
    let v = build_pair(off, h);
    v
}
// </vc-code>


}
fn main() {}