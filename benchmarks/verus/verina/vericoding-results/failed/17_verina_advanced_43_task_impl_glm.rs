// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max_strength(nums: &Vec<i32>) -> (result: i32)
    requires nums.len() > 0,
    ensures

        exists|i: int| 0 <= i < nums.len() && result >= nums[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed invariant block syntax */
    let mut max = nums[0];
    for i in 1..nums.len()
        invariant {
            0 <= i as int,
            i as int <= nums.len() as int,
            max >= nums[0],
        }
    {
        if nums[i] > max {
            max = nums[i];
        }
    }
    max
}
// </vc-code>

}
fn main() {}