// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn id_f32(x: f32) -> f32 { x }
// </vc-helpers>

// <vc-spec>
fn sin(x: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() > 0,
    ensures result.len() == x.len()
// </vc-spec>
// <vc-code>
{
    x
}
// </vc-code>

}
fn main() {}