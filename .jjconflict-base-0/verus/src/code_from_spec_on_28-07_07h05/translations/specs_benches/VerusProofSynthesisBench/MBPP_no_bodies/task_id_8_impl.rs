use vstd::prelude::*;

verus! {

fn square_nums(nums: &Vec<i32>) -> (squared: Vec<i32>)
    // pre-conditions-start
    requires
        forall|k: int|
            0 <= k < nums.len() ==> (0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        nums.len() == squared.len(),
        forall|k: int| 0 <= k < nums.len() ==> (#[trigger] squared[k] == nums[k] * nums[k]),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 3): fixed trigger annotation in loop invariant */
    while i < nums.len()
        invariant
            i <= nums.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == nums[k] * nums[k],
            /* code modified by LLM (iteration 3): added proper trigger annotations */
            forall|k: int| 0 <= k < nums.len() ==> (0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX),
        decreases nums.len() - i,
    {
        /* code modified by LLM (iteration 3): added assertion to help with overflow check */
        assert(0 <= i < nums.len());
        assert(0 <= nums[i as int] * nums[i as int] < i32::MAX);
        
        let squared_val = nums[i] * nums[i];
        result.push(squared_val);
        
        /* code modified by LLM (iteration 3): added assertion to maintain invariant */
        assert(result.len() == i + 1);
        assert(result[i as int] == nums[i as int] * nums[i as int]);
        
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}