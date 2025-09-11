// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn find_max(x: int, y: int) -> int {
    if x > y { x } else { y }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: &Vec<i32>) -> (max: i32)
    requires 
        1 <= nums.len() <= 2500,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] >= -10000 && #[trigger] nums[i] <= 10000,

    ensures 
        max >= 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}