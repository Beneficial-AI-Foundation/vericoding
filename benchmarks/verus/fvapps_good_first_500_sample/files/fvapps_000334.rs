// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sqrt(n: u32) -> (result: u32)
    ensures result * result <= n && (result + 1) * (result + 1) > n
{
    // impl-start
    assume(false);
    0
    // impl-end
}

fn num_squares(n: u32) -> (result: u32)
    requires n >= 1,
    ensures 
        result >= 1 && result <= 4
{
    // impl-start
    assume(false);
    1
    // impl-end
}
// </vc-spec>
// <vc-code>
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded_and_plausible
    
    // println!("{}", num_squares(12)); // Expected: 3
    // println!("{}", num_squares(13)); // Expected: 2
    // println!("{}", num_squares(7));  // Expected: 4
}