// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed lemma to match actual loop invariant */
spec fn is_valid_max(nums: &Vec<i32>, max_val: i32) -> bool {
    nums.len() > 0 &&
    (exists|i: int| 0 <= i < nums.len() && max_val >= nums[i])
}

proof fn lemma_max_exists(nums: &Vec<i32>, max_val: i32)
    requires
        nums.len() > 0,
        exists|j: int| 0 <= j < nums.len() && max_val >= nums[j]
    ensures is_valid_max(nums, max_val)
{
    assert(exists|i: int| 0 <= i < nums.len() && max_val >= nums[i]);
}
// </vc-helpers>

// <vc-spec>
fn max_strength(nums: &Vec<i32>) -> (result: i32)
    requires nums.len() > 0,
    ensures

        exists|i: int| 0 <= i < nums.len() && result >= nums[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): removed witness_idx parameter from lemma call */
    let mut max_val = nums[0];
    let mut i = 1;
    
    while i < nums.len()
        invariant
            0 < i <= nums.len(),
            exists|j: int| 0 <= j < i && max_val >= nums[j]
        decreases nums.len() - i
    {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }
    
    proof {
        lemma_max_exists(nums, max_val);
    }
    
    max_val
}
// </vc-code>

}
fn main() {}