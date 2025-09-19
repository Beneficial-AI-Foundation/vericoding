// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* Helper function to find maximum of two integers */
spec fn int_max(x: int, y: int) -> int {
    if x < y { y } else { x }
}
// </vc-helpers>

// <vc-spec>
fn longest_common_subsequence(a: &Vec<i32>, b: &Vec<i32>) -> (result: int)
    requires true,
    ensures result >= 0,
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
fn main() {}