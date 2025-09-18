// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_true(b: bool) -> bool { b == true }
proof fn true_proof() ensures is_true(true) && !is_true(false) { }
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
    proof {
        true_proof();
    }
    true
}
// </vc-code>

}
fn main() {}