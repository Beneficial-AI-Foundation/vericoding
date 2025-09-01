use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn max_array(nums: &[i32]) -> (idx: usize)
    // pre-conditions-start
    requires
        nums.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= idx && idx < nums.len(),
        forall|i: int| 0 <= i && i < nums.len() ==> nums[i] <= nums[idx as int],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < nums.len()
        invariant
            0 <= max_idx < nums.len(),
            1 <= i <= nums.len(),
            forall|j: int| 0 <= j && j < i ==> nums[j] <= nums[max_idx as int],
        decreases nums.len() - i,
    {
        if nums[i] > nums[max_idx] {
            max_idx = i;
        }
        i = i + 1;
    }
    
    max_idx
}
// </vc-code>

fn main() {}
}