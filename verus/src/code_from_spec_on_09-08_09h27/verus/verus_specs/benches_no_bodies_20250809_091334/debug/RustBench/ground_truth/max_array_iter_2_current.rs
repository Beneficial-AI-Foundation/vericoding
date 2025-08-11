use vstd::prelude::*;

verus! {

fn max_array(nums: &[i32]) -> (idx: usize)
    requires
        nums.len() >= 1,
    ensures
        0 <= idx && idx < nums.len(),
        forall|i: int| 0 <= i && i < nums.len() ==> nums[i] <= nums[idx as int],
{
    let mut max_idx = 0;
    let mut i = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < nums.len()
        invariant
            0 <= max_idx < nums.len(),
            1 <= i <= nums.len(),
            forall|j: int| 0 <= j < i ==> nums[j] <= nums[max_idx as int],
        decreases nums.len() - i,
    {
        if nums[i] > nums[max_idx] {
            max_idx = i;
        }
        i += 1;
    }
    
    max_idx
}

fn main() {}
}