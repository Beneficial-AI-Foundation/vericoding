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
    let mut max = nums[0];
    let mut i = 1;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
        invariant
            forall|j: int| 0 <= j < i ==> max >= nums[j],
    {
        if nums[i] > max {
            max = nums[i];
        }
        i = i + 1;
    }
    max
}
// </vc-code>

}
fn main() {}