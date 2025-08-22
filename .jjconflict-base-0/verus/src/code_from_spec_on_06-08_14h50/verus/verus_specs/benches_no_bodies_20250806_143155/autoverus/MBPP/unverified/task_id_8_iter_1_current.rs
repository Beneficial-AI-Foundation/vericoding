use vstd::prelude::*;

fn main() {}

verus! {

fn square_nums(nums: &Vec<i32>) -> (squared: Vec<i32>)
    requires
        forall|k: int|
            0 <= k < nums.len() ==> (0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX),
    ensures
        nums.len() == squared.len(),
        forall|k: int| 0 <= k < nums.len() ==> (#[trigger] squared[k] == nums[k] * nums[k]),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < nums.len()
        invariant
            i <= nums.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == nums[k] * nums[k],
    {
        let square = nums[i] * nums[i];
        result.push(square);
        i += 1;
    }
    
    result
}

} // verus!