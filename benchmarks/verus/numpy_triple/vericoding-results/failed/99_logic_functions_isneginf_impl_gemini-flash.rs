// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed `spec` declaration from the helper section. */
uninterp spec fn is_neg_infinity(x: f32) -> bool { x == f32::NEG_INFINITY }
// </vc-helpers>

// <vc-spec>
spec fn is_neg_infinity(x: f32) -> bool;

fn isneginf(x: Vec<f32>) -> (result: Vec<bool>)
    requires x@.len() > 0,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < x@.len() ==> {
            &&& (result@[i] == is_neg_infinity(x@[i]))
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No change */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: int = 0;

    while i < x@.len()
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == is_neg_infinity(x@[j]),
            i <= x@.len()
    {
        result.push(is_neg_infinity(x@[i]));
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}