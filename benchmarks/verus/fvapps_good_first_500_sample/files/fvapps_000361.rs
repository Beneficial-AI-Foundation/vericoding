// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn gcd(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 { a } else { gcd(b, a % b) }
}

spec fn have_common_factor(a: nat, b: nat) -> bool {
    gcd(a, b) > 1
}

fn largest_component_size(nums: Vec<nat>) -> (result: nat)
    requires nums.len() > 0,
    ensures 
        result > 0,
        result <= nums.len(),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


/* Apps difficulty: interview */
/* Assurance level: unguarded */

/*
fn test_examples() {
    // Example 1: [4,6,15,35] should output 4
    // Example 2: [20,50,9,63] should output 2  
    // Example 3: [2,3,6,7,4,12,21,39] should output 8
}
*/

}

fn main() {}