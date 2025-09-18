// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn not_true_is_false() ensures !true == false { }

proof fn trivial_true() ensures true { }
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
    let result = false;
    proof {
        assert(result == !true);
    }
    result
}
// </vc-code>

}
fn main() {}