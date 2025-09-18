// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate definition of is_neg_infinity; keep spec declaration in <vc-spec> */
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
    /* code modified by LLM (iteration 5): iterate over Vec<f32> and push boolean indicating -inf using to_bits */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x.len() {
        invariant(i <= x.len());
        invariant(result.len() == i);
        decreases(x.len() - i);
        let b: bool = x[i].to_bits() == 0xff800000u32;
        result.push(b);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}