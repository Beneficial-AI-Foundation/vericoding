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
    /* code modified by LLM (iteration 2): Fixed compilation error by replacing incorrect range indexing with forall quantifier in loop invariant to check result is >= all elements in prefix */
    let mut result = nums[0];
    let mut i = 1;
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            forall |j: int| 0 <= j < i ==> result >= nums@[j],
        decreases nums.len() - i
    {
        if nums[i] > result {
            result = nums[i];
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}