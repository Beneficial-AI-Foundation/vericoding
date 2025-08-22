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
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to fix compilation error */
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == nums[j] * nums[j] * nums[j],
        decreases nums.len() - i
    {
        let cube = nums[i] * nums[i] * nums[i];
        result.push(cube);
        i += 1;
    }
    
    result
}

} // verus!