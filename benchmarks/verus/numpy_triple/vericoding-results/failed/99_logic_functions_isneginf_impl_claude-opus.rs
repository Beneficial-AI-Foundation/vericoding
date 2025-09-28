// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed extern_spec_std and use builtin spec function */
builtin_macros::verus_proof_macro_exprs! {
    spec fn is_neg_infinity(x: f32) -> bool {
        x == f32::NEG_INFINITY
    }
}

exec fn is_neg_infinity_exec(x: f32) -> (result: bool)
    ensures result == is_neg_infinity(x)
{
    proof {
        builtin_macros::verus_proof_macro_exprs! {
            assert(is_neg_infinity(x) == (x == f32::NEG_INFINITY));
        }
    }
    x == f32::NEG_INFINITY
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
    /* code modified by LLM (iteration 5): Implementation using helper function */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == is_neg_infinity(x@[j])
    {
        let is_neg_inf = is_neg_infinity_exec(x[i]);
        result.push(is_neg_inf);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}