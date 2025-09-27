// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_equal_sticks(n: nat) -> (result: nat)
    requires n >= 1,
    ensures 
        result == (n + 1) / 2,
        result <= n,
        result >= 1
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // assert(max_equal_sticks(1) == 1);
    // assert(max_equal_sticks(3) == 2);
    // assert(max_equal_sticks(4) == 2);
}