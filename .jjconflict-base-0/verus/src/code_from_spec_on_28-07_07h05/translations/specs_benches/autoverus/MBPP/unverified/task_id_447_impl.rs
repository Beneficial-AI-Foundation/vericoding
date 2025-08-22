use vstd::prelude::*;

fn main() {}

verus! {

//IMPL cube_element
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
    
    /* code modified by LLM (iteration 1): added decreases clause and proper invariants for overflow safety */
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == nums[j] * nums[j] * nums[j],
        decreases nums.len() - i,
    {
        /* code modified by LLM (iteration 1): assert preconditions to help verifier with overflow checks, cast usize to int */
        assert(0 <= i < nums.len());
        assert(i32::MIN <= nums[i as int] * nums[i as int] <= i32::MAX);
        let squared_val = nums[i] * nums[i];
        
        assert(i32::MIN <= squared_val * nums[i as int] <= i32::MAX);
        let cubed_val = squared_val * nums[i];
        
        result.push(cubed_val);
        i += 1;
    }
    
    result
}

} // verus!