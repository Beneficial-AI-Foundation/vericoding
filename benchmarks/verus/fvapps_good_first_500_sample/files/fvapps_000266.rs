// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn log2_upper_bound(n: nat) -> nat 
    decreases n
{
    if n <= 1 { 0 } else { 1 + log2_upper_bound(n / 2) }
}

fn racecar(target: nat) -> (result: nat)
    requires target > 0,
    ensures 
        result > 0,
        result <= 4 * log2_upper_bound(target),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


/* Apps difficulty: interview
   Assurance level: unguarded */

}

fn main() {
    // assert(racecar(3) == 2);
    // assert(racecar(6) == 5);
    // assert(racecar(4) == 5);
}