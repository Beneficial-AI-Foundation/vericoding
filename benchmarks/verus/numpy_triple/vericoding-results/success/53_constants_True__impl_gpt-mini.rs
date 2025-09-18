// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn not_true_eq_false() ensures !true == false { }
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