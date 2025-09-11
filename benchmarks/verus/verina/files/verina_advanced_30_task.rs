// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn longest_increasing_streak(nums: &Vec<i32>) -> (result: usize)
    ensures
        (nums.len() == 0 ==> result == 0),
        result <= nums.len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}