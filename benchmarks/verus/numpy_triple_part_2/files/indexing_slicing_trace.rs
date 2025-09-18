// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn trace(a: Vec<Vec<f32>>, offset: i32) -> (result: f32)
    ensures true
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}
// </vc-code>


}
fn main() {}