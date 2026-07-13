// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_pow2(n: nat) -> bool {
    exists|k: nat| n == pow(2, k)
}

fn solve_arena_of_greed(n: nat) -> (result: nat)
    requires n > 0,
    ensures 
        result <= n,
        result <= (n + 1) / 2 + n / 2,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0nat
    // impl-end
}
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded_and_plausible
    
    // Example test cases:
    // solve_arena_of_greed(5) should return 2
    // solve_arena_of_greed(6) should return 4  
    // solve_arena_of_greed(8) should return 5
}