// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec sequence mapping of is_neg_infinity over a Seq */
spec fn map_is_neg_infinity(xs: Seq<f32>) -> Seq<bool> { Seq::new(xs.len(), |i: int| is_neg_infinity(xs[i])) }
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
    /* code modified by LLM (iteration 5): construct result from spec sequence using Vec::from_spec_seq */
    let result: Vec<bool> = Vec::from_spec_seq(Ghost(map_is_neg_infinity(x@)));
    result
}
// </vc-code>

}
fn main() {}