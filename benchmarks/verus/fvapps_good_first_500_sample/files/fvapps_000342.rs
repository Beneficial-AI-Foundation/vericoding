// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn broken_calc(start: nat, target: nat) -> (result: nat)
    requires
        1 <= start <= 1000000000,
        1 <= target <= 1000000000,
    ensures
        result >= 0,
        start == target ==> result == 0,
        start > target ==> result == start - target,
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
    // Apps difficulty: interview
    // Assurance level: guarded_and_plausible

    // #eval broken_calc 2 3  // Expected: 2
    // #eval broken_calc 5 8  // Expected: 2 
    // #eval broken_calc 3 10 // Expected: 3
}