// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use spec function with uninterp attribute */
#[spec] fn is_neg_infinity_impl(x: f32) -> bool {
    uninterp
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
    /* code modified by LLM (iteration 5): implement concrete logic for negative infinity check */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == is_neg_infinity(x[j])
    {
        let neg_inf_check = x[i].is_infinite() && x[i].is_sign_negative();
        result.push(neg_inf_check);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}