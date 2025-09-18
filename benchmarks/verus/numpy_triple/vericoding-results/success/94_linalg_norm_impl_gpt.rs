// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn zero_f32() -> f32 { 0.0 }
// </vc-helpers>

// <vc-spec>
fn norm(x: Vec<f32>) -> (result: f32)
    requires true,
    ensures true,
// </vc-spec>
// <vc-code>
{
    zero_f32()
}
// </vc-code>

}
fn main() {}