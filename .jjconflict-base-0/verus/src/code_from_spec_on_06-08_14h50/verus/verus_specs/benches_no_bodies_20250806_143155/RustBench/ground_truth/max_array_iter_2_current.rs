use vstd::prelude::*;

verus! {

fn max_array(nums: &[i32]) -> (idx: usize)
    requires
        nums.len() >= 1,
    ensures
        0 <= idx && idx < nums.len(),
        forall|i: int| 0 <= i && i < nums.len() ==> nums[i] <= nums[idx as int],
{
    let mut max_idx: usize = 0;
    let mut j: usize = 1;
    
    while j < nums.len()
        invariant
            0 <= max_idx && max_idx < nums.len(),
            1 <= j && j <= nums.len(),
            forall|i: int| 0 <= i && i < j ==> nums[i] <= nums[max_idx as int],
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        decreases nums.len() - j
    {
        if nums[j] > nums[max_idx] {
            max_idx = j;
        }
        j += 1;
    }
    
    max_idx
}

fn main() {}
}