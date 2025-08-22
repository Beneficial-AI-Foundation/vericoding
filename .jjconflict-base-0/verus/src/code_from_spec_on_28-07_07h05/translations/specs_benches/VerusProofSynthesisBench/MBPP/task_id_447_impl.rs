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
    
    /* code modified by LLM (iteration 2): added proper invariants, bounds checking, and decreases clause */
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            result.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result[j] == nums[j] * nums[j] * nums[j],
        decreases nums.len() - i,
    {
        /* code modified by LLM (iteration 2): use preconditions to establish bounds with proper triggers */
        assert(0 <= i < nums.len());
        // The preconditions guarantee these bounds hold for all valid indices
        assert(forall|k: int| 0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k] <= i32::MAX));
        assert(forall|k: int| 0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k] * #[trigger] nums[k] <= i32::MAX));
        // Since i is a valid index, the bounds hold for nums[i]
        assert(i32::MIN <= nums[i as int] * nums[i as int] <= i32::MAX);
        assert(i32::MIN <= nums[i as int] * nums[i as int] * nums[i as int] <= i32::MAX);
        
        let cubed_value = nums[i] * nums[i] * nums[i];
        result.push(cubed_value);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}