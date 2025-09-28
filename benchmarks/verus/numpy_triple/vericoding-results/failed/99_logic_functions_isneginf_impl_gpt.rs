// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): mapping from Seq<f32> to Seq<bool> using is_neg_infinity */
pub open spec fn map_isneginf(s: Seq<f32>) -> Seq<bool> {
    Seq::new(s.len(), |i: int| is_neg_infinity(s[i]))
}
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
{
    /* code modified by LLM (iteration 5): map sequence and build Vec using Vec::from_seq */
    let s: Seq<bool> = map_isneginf(x@);
    let result: Vec<bool> = Vec::from_seq(s);
    result
}
// </vc-code>

}
fn main() {}