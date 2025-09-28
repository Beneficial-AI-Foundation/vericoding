// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial reflexivity lemma for is_neg_infinity */
proof fn lemma_is_neg_infinity_reflexive(x: f32)
    ensures
        is_neg_infinity(x) == is_neg_infinity(x),
{
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
    /* code modified by LLM (iteration 5): iterate using usize runtime index and ghost-level invariants */
    let mut result: Vec<bool> = Vec::new();
    let n_usize: usize = x.len();
    let mut i: usize = 0usize;
    while i < n_usize
        invariant
            0 <= (i as int),
            (i as int) <= x@.len(),
            result@.len() == (i as nat),
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == is_neg_infinity(x@[j]),
        decreases x@.len() - (i as int)
    {
        let b: bool = is_neg_infinity(x@[i as int]);
        result.push(b);
        i = i + 1usize;
    }
    result
}

// </vc-code>

}
fn main() {}