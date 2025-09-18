// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn id_bool(b: bool) -> bool { b }

proof fn lemma_not_true_false() ensures !true == false { }
// </vc-helpers>

// <vc-spec>
fn true_() -> (result: bool)
    ensures 
        result == true,
        true, // Boolean properties hold by definition
        !result == false
// </vc-spec>
// <vc-code>
{
    true
}
// </vc-code>

}
fn main() {}