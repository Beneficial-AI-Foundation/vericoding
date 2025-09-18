// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_nonneg(x: int) -> bool { x >= 0 }
proof fn lemma_add_zero(x: int) ensures x + 0 == x { }
// </vc-helpers>

// <vc-spec>
fn numpy_rint(x: Vec<f32>) -> (result: Vec<f32>)
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