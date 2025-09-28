// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn vec2(a: f32, b: f32) -> (result: Vec<f32>)
    ensures
        result@.len() == 2,
        result@[0] == a,
        result@[1] == b,
{
    let mut v: Vec<f32> = Vec::new();
    v.push(a);
    v.push(b);
    v
}
// </vc-helpers>

// <vc-spec>
fn legline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures
        result@.len() == 2,
        result@[0] == off,
        result@[1] == scl
// </vc-spec>
// <vc-code>
{
    let v = vec2(off, scl);
    v
}
// </vc-code>

}
fn main() {}