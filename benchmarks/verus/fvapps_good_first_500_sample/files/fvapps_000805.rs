// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power2::pow2;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_barbecue_sticks(n: nat) -> (result: nat)
    requires n >= 3,
    ensures 
        result > 0,
        result % 2 == 1,
        result >= pow2((n - 2) as nat)
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
    // #eval solve_barbecue_sticks 4  // Expected: 5
    // #eval solve_barbecue_sticks 5  // Expected: 9  
    // #eval solve_barbecue_sticks 6  // Expected: 17
}