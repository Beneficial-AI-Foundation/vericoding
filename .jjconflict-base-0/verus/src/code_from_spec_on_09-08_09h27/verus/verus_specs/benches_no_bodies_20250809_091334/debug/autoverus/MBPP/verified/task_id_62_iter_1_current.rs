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
    let mut j = 1;
    
    while j < nums.len()
        invariant
            1 <= j <= nums.len(),
            forall|i: int| 0 <= i < j ==> min <= nums[i],
            exists|i: int| 0 <= i < j && min == nums[i],
    {
        if nums[j] < min {
            min = nums[j];
        }
        j += 1;
    }
    
    min
}

} // verus!