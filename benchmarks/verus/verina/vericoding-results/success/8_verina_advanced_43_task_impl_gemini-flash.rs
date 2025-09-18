// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): ensures correct max of two i32 numbers */
fn max(a: i32, b: i32) -> (result: i32)
    ensures (result == a) || (result == b),
            result >= a,
            result >= b,
{
    if a > b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn max_strength(nums: &Vec<i32>) -> (result: i32)
    requires nums.len() > 0,
    ensures

        exists|i: int| 0 <= i < nums.len() && result >= nums[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed loop invariants regarding current_max and nums[0] */
{
    let mut current_max = nums[0];
    let mut i = 1;
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            current_max >= nums[0],
            forall|j: int| 0 <= j < i ==> current_max >= nums[j],
        decreases nums.len() - i
    {
        current_max = max(current_max, nums[i]);
        i = i + 1;
    }
    current_max
}
// </vc-code>

}
fn main() {}