// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added uninterp spec function and exec implementation */
spec fn is_neg_infinity(x: f32) -> bool
    uninterp;

fn is_neg_infinity_impl(x: f32) -> (result: bool)
    ensures result == is_neg_infinity(x)
{
    x.is_infinite() && x.is_sign_negative()
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
    /* code modified by LLM (iteration 5): use exec implementation instead of direct f32 methods */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == is_neg_infinity(x@[j]),
    {
        let is_neg_inf = is_neg_infinity_impl(x[i]);
        result.push(is_neg_inf);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}