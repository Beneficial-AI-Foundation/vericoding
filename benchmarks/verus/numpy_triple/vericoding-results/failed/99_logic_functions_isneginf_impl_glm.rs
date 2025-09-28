// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
exec fn is_neg_infinity_exec(x: f32) -> bool {
    /* helper modified by LLM (iteration 4): implemented negative infinity check as exec function */
    f32::to_bits(x) == 0xFF800000u32
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
    /* code modified by LLM (iteration 4): use exec function instead of spec function */
    let mut i = 0;
    let mut result = Vec::new();
    while i < x.len()
        invariant
            i <= x@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == is_neg_infinity_exec(x@[j]),
        decreases x@.len() - i
    {
        result.push(is_neg_infinity_exec(x[i]));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}