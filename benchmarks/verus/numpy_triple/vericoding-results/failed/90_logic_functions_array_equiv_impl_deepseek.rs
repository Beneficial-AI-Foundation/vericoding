// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed ghost indexing by using ghost variables and proper conversions */
#[verifier::spec]
fn array_equiv_helper(a1: Vec<f32>, a2: Vec<f32>, idx: nat) -> (result: bool)
    requires
        idx <= a1@.len(),
        a1@.len() == a2@.len(),
    ensures
        result == (forall|i: int| idx <= i < a1@.len() ==> a1@[i] == a2@[i]),
    decreases a1@.len() - idx
{
    if idx >= a1@.len() {
        true
    } else {
        ghost {
            let ghost_idx = idx as int;
            if a1@[ghost_idx] != a2@[ghost_idx] {
                false
            } else {
                array_equiv_helper(a1, a2, (idx + 1) as nat)
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn array_equiv(a1: Vec<f32>, a2: Vec<f32>) -> (result: bool)
    requires a1.len() == a2.len(),
    ensures result == (forall|i: int| 0 <= i < a1@.len() ==> a1@[i] == a2@[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed ghost code usage by calling helper function properly */
{
    proof {
        let ghost_result = array_equiv_helper(a1, a2, 0 as nat);
        ghost_result
    }
}
// </vc-code>

}
fn main() {}