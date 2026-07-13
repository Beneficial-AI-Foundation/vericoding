// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_broken_calc(l: nat, r: nat) -> (result: nat)
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

proof fn same_value(x: nat) {
    // impl-start  
    assume(false);
    // impl-end
}

proof fn consecutive_valid(x: nat) {
    // impl-start
    assume(false);
    // impl-end
}

proof fn range_validity(l: nat, r: nat) {
    // impl-start
    assume(false);
    // impl-end
}
// </vc-spec>
// <vc-code>
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    // #eval solve_broken_calc 1 4
    // Expected output: 8

    // #eval solve_broken_calc 323 323  
    // Expected output: 0

    // #eval solve_broken_calc 1 1000000
    // Expected output: 3439863766
}