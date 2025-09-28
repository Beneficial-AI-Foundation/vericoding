// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_pair(a: f32, b: f32) -> (result: Vec<f32>)
    ensures
        result.len() == 2,
{
    let mut v = Vec::<f32>::new();
    v.push(a);
    v.push(b);
    v
}
// </vc-helpers>

// <vc-spec>
fn lagline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures result.len() == 2
// </vc-spec>
// <vc-code>
{
    let v = make_pair(off, scl);
    v
}
// </vc-code>

}
fn main() {}