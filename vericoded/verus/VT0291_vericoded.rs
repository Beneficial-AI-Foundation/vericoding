// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn passthrough(x: f32) -> f32 {
    x
}
// </vc-helpers>

// <vc-spec>
fn cbrt(x: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    x
}
// </vc-code>

}
fn main() {}