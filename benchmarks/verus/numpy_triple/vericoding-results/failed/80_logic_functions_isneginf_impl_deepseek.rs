// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Keep only the implementation and remove duplicate declaration */
spec fn is_neg_infinity(x: f32) -> bool { x == -1.0f32 / 0.0f32 }
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
/* code modified by LLM (iteration 5): Use proper sequence indexing syntax with @ operator */
{
    let mut result = Vec::with_capacity(x.len());
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == is_neg_infinity(x@[j])
    {
        result.push(is_neg_infinity(x@[i]));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}