// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): confirmed spec fn implementation */
spec fn is_neg_infinity(x: f32) -> bool {
    x == f32::NEG_INFINITY
}
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
{
/* code modified by LLM (iteration 3): corrected indentation for loop body to fix compilation error */
    let ghost len_: int = x.len() as int;
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant 0 <= i <= x.len()
        invariant result.len() == i
        invariant forall |j: int| 0 <= j < i ==> result@[j] == is_neg_infinity(x@[j])
        decreases len_ - i
    {
        result.push(is_neg_infinity(x[i]));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}