// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_nice_staircases_spec(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        1
    }
}

fn count_nice_staircases(n: nat) -> (result: nat)
    ensures 
        n > 0 ==> result > 0,
        result <= n,
        result == count_nice_staircases_spec(n)
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

    // #guard_msgs in
    // #eval count_nice_staircases 1

    // #guard_msgs in  
    // #eval count_nice_staircases 8

    // #guard_msgs in
    // #eval count_nice_staircases 6

    // #guard_msgs in
    // #eval count_nice_staircases 1000000000000000000
}