// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_training_camp(n: nat, m: nat) -> (result: nat)
    requires n >= 1,
    ensures 
        result >= 0,
        n == 1 ==> result == 0,
        n == 2 ==> result == m,
        n > 2 && m == 0 ==> result == (n - 3)
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

    // Example test cases:
    // solve_training_camp(2, 1) should return 1
    // solve_training_camp(3, 2) should return 4  
    // solve_training_camp(1, 5) should return 0
}