// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn trap(heights: Vec<usize>) -> (result: usize)
    ensures 
        heights.len() == 0 ==> result == 0,
        heights.len() == 1 ==> result == 0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded_and_plausible

    // Example: trap([0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]) should return 6
    // Example: trap([4, 2, 0, 3, 2, 5]) should return 9
    // Example: trap([]) should return 0
}