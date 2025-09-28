// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn create_vec(x: f32, y: f32) -> (result: Vec<f32>)
    ensures result.len() == 2
{
    let mut v = Vec::new();
    v.push(x);
    v.push(y);
    v
}
// </vc-helpers>

// <vc-spec>
fn lagline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures result.len() == 2
// </vc-spec>
// <vc-code>
{
    create_vec(off, scl)
}
// </vc-code>

}
fn main() {}