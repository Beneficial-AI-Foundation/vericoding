use vstd::prelude::*;

fn main() {}

verus! {

fn cube_element(nums: &Vec<i32>) -> (cubed: Vec<i32>)
    requires
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                <= i32::MAX),
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                * #[trigger] nums[k] <= i32::MAX),
    ensures
        forall|i: int|
            0 <= i < nums.len() ==> cubed[i] == #[trigger] nums[i] * #[trigger] nums[i]
                * #[trigger] nums[i],
{
    let mut result = Vec::new();
    let mut index = 0;
    
    while index < nums.len()
        invariant
            index <= nums.len(),
            result.len() == index,
            forall|i: int| 0 <= i < index ==> result[i] == nums[i] * nums[i] * nums[i]
    {
        let cube = nums[index] * nums[index] * nums[index];
        result.push(cube);
        index += 1;
    }
    
    result
}

} // verus!