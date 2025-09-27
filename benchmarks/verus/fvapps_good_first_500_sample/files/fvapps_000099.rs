// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_candies(r: nat, g: nat, b: nat) -> (result: nat)
    ensures 
        result >= 0,
        result <= r + g,
        result <= r + b,
        result <= g + b,
        result <= (r + g + b) / 2,
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

    // Tests for solve_candies function
    // assert(solve_candies(1, 1, 1) == 1);
    // assert(solve_candies(1, 2, 1) == 2);
    // assert(solve_candies(7, 4, 10) == 10);
}