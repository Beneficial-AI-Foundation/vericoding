use vstd::prelude::*;

fn main() {
}

verus! {

fn smallest_num(nums: &Vec<i32>) -> (min: i32)
    requires
        nums.len() > 0,
    ensures
        forall|i: int| 0 <= i < nums.len() ==> min <= nums[i],
        exists|i: int| 0 <= i < nums.len() && min == nums[i],
{
    let mut min = nums[0];
    let mut idx = 1;
    
    while idx < nums.len()
        invariant
            1 <= idx <= nums.len(),
            forall|i: int| 0 <= i < idx ==> min <= nums[i],
            exists|i: int| 0 <= i < idx && min == nums[i],
    {
        if nums[idx] < min {
            min = nums[idx];
        }
        idx += 1;
    }
    
    min
}

} // verus!