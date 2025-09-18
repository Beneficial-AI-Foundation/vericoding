// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn is_neg_infinity(x: f32) -> bool;

fn isneginf(x: Vec<f32>) -> (result: Vec<bool>)
    requires x.len() > 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> {
            &&& (result[i] == is_neg_infinity(x[i]))
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use usize-based loop and cast to int in invariant */
{
    let mut result = Vec::with_capacity(x.len());
    for idx in 0..x.len()
        invariant
            result.len() == idx,
            forall|j: int| 0 <= j < idx as int ==> result@[j] == is_neg_infinity(x@[j])
    {
        let b = x[idx] == f32::NEG_INFINITY;
        assert(b == is_neg_infinity(x[idx]));
        result.push(b);
    }
    result
}
// </vc-code>

}
fn main() {}