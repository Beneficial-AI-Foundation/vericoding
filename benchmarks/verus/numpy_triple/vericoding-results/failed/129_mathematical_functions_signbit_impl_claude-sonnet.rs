// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_negative(x: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add uninterp marker for spec function */
spec fn is_negative(x: f32) -> bool
    uninterp
// </vc-helpers>

// <vc-spec>
fn signbit(x: Vec<f32>) -> (result: Vec<bool>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == is_negative(x[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix postcondition by using x@[i] indexing and maintaining loop invariant */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == is_negative(x@[j]),
        decreases x.len() - i
    {
        let sign_bit = x[i] < 0.0;
        result.push(sign_bit);
        proof {
            assert(result@[i as int] == sign_bit);
            assert(sign_bit == is_negative(x@[i as int]));
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}