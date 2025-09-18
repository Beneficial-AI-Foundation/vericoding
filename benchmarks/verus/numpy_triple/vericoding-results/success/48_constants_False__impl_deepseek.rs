// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn false_lemma() ensures false == !true { }
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
        false_lemma();
    }
    false
}
// </vc-code>

}
fn main() {}