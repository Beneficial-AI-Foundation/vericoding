// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_rollaxis_identity(a: Vec<f32>, axis: i32, start: i32) ensures a == a {}
// </vc-helpers>

// <vc-spec>
fn numpy_rollaxis(a: Vec<f32>, axis: i32, start: i32) -> (result: Vec<f32>)
    ensures result == a
// </vc-spec>
// <vc-code>
{
    proof { lemma_rollaxis_identity(a, axis, start); }
    a
}
// </vc-code>

}
fn main() {}