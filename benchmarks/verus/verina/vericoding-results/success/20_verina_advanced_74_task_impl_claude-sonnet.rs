// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed invariant to properly maintain max_val bounds */
fn find_max(nums: &Vec<u32>) -> (max_val: u32)
    requires
        nums.len() > 0,
        forall|i: int| 0 <= i < nums.len() ==> nums[i] >= 1 && nums[i] <= 100,
    ensures
        max_val >= 1 && max_val <= 100,
        exists|i: int| 0 <= i < nums.len() && nums[i] == max_val,
        forall|i: int| 0 <= i < nums.len() ==> nums[i] <= max_val,
{
    let mut max_val = nums[0];
    let mut idx = 1;
    
    while idx < nums.len()
        invariant
            1 <= idx <= nums.len(),
            max_val >= 1 && max_val <= 100,
            exists|i: int| 0 <= i < idx && nums[i] == max_val,
            forall|i: int| 0 <= i < idx ==> nums[i] <= max_val,
            forall|i: int| 0 <= i < nums.len() ==> nums[i] >= 1 && nums[i] <= 100,
        decreases nums.len() - idx
    {
        if nums[idx] > max_val {
            max_val = nums[idx];
        }
        idx += 1;
    }
    
    max_val
}
// </vc-helpers>

// <vc-spec>
fn solution(nums: Vec<u32>) -> (result: u32)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] >= 1 && #[trigger] nums[i] <= 100,
    ensures
        result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): no changes needed */
    let max_val = find_max(&nums);
    max_val
}
// </vc-code>

}
fn main() {}