use vstd::prelude::*;

verus! {

fn cube_element(nums: &Vec<i32>) -> (cubed: Vec<i32>)
    // pre-conditions-start
    requires
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                <= i32::MAX),
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                * #[trigger] nums[k] <= i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int|
            0 <= i < nums.len() ==> cubed[i] == #[trigger] nums[i] * #[trigger] nums[i]
                * #[trigger] nums[i],
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause and updated invariant with auto trigger */
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            result.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result[j] == nums[j] * nums[j] * nums[j],
        decreases nums.len() - i,
    {
        /* code modified by LLM (iteration 1): removed unused ghost type cast */
        
        let square = nums[i] * nums[i];
        let cube = square * nums[i];
        result.push(cube);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}