// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_not_true_is_false() ensures !true == false { }
// </vc-helpers>

// <vc-spec>
fn false_() -> (result: bool)
    ensures 
        result == false,
        true, // Boolean properties hold by definition
        result == !true
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_not_true_is_false();
    }
    false
}
// </vc-code>

}
fn main() {}