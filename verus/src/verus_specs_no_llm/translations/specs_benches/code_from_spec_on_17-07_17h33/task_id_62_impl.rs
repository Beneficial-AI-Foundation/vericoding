use vstd::prelude::*;

verus! {

//IMPL smallest_num
/* code modified by LLM (iteration 2): Fixed function signature and moved requires/ensures clauses to correct position */
fn smallest_num(nums: &Vec<i32>) -> i32
    requires
        nums.len() > 0,
    ensures |min: i32|
        forall|i: int| 0 <= i < nums.len() ==> min <= nums[i],
        exists|i: int| 0 <= i < nums.len() && min == nums[i],
{
    /* code modified by LLM (iteration 2): Implemented proper algorithm to find minimum value */
    let mut min = nums[0];
    let mut j = 1;
    
    while j < nums.len()
        invariant
            0 < j <= nums.len(),
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

fn main() {}