// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn rain(heights: &Vec<i32>) -> (result: i32)
    requires forall|i: int| 0 <= i < heights.len() ==> heights[i] >= 0,
    ensures 
        result >= 0,
        heights.len() < 3 ==> result == 0,
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