// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_max_in_vec(val: i32, nums: &Vec<i32>) -> bool {
    exists|i: int| 0 <= i < nums.len() && val == nums[i] &&
    forall|j: int| 0 <= j < nums.len() ==> nums[j] <= val
}

proof fn max_exists_lemma(nums: &Vec<i32>)
    requires nums.len() > 0
    ensures exists|i: int| 0 <= i < nums.len() && forall|j: int| 0 <= j < nums.len() ==> nums[j] <= nums[i]
{
    let mut max_idx = 0int;
    let mut k = 0int;
    while k < nums.len()
        invariant 0 <= k <= nums.len(),
        invariant 0 <= max_idx < nums.len(),
        invariant forall|j: int| 0 <= j < k ==> nums[j] <= nums[max_idx]
    {
        if nums[k] > nums[max_idx] {
            max_idx = k;
        }
        k = k + 1;
    }
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
    /* code modified by LLM (iteration 5): fixed loop invariants syntax */
    let mut max_val = nums[0];
    let mut i = 1;
    
    while i < nums.len()
        invariant 1 <= i <= nums.len(),
        invariant exists|j: int| 0 <= j < i && max_val == nums[j],
        invariant forall|j: int| 0 <= j < i ==> nums[j] <= max_val
    {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i = i + 1;
    }
    
    max_val
}
// </vc-code>

}
fn main() {}