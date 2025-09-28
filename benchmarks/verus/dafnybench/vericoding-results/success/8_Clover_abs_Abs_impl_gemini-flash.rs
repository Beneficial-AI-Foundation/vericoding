use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
proof fn abs(x: int) -> (y: int)
    ensures 
        x >= 0 ==> x == y,
        x < 0 ==> x + y == 0,
// </vc-spec>
// <vc-code>
{
    if x >= 0 {
        x
    } else {
        // Assertions in an `else` branch are typically for proving properties of the branch itself.
        // The property `x + (-x) == 0` is a basic arithmetic truth that Verus can deduce.
        // No explicit proof block is needed here for this simple arithmetic.
        -x
    }
}
// </vc-code>

fn main() {
}

}