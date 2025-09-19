// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn integer_replacement(n: u32) -> (result: u32)
    requires n > 0
    ensures 
        result >= 0,
        n == 1 ==> result == 0,
        n == 2 ==> result == 1
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

    // println!("{}", integer_replacement(8)); // Should output 3
    // println!("{}", integer_replacement(7)); // Should output 4
    // println!("{}", integer_replacement(3)); // Should output 2
}