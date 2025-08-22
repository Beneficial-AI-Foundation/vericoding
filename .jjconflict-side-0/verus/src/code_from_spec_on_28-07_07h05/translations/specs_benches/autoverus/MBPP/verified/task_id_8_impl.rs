use vstd::prelude::*;

fn main() {
    // Example usage
    let nums = vec![1, 2, 3, 4];
    let squared = square_nums(&nums);
    println!("{:?}", squared);
}

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
    
    /* code modified by LLM (iteration 3): fixed loop invariant and added proper bounds checking */
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == nums[k] * nums[k],
        decreases nums.len() - i,
    {
        /* code modified by LLM (iteration 3): use precondition to ensure no overflow with proper type casting */
        assert(0 <= nums[i as int] * nums[i as int] < i32::MAX);
        let square = nums[i as int] * nums[i as int];
        result.push(square);
        
        /* code modified by LLM (iteration 3): help prove invariant is maintained with proper type casting */
        assert(result.len() == i + 1);
        assert(result[i as int] == nums[i as int] * nums[i as int]);
        assert(forall|k: int| 0 <= k < i ==> result[k] == nums[k] * nums[k]);
        
        i += 1;
    }
    
    /* code modified by LLM (iteration 3): final assertions to establish postcondition */
    assert(result.len() == nums.len());
    assert(i == nums.len());
    assert(forall|k: int| 0 <= k < nums.len() ==> result[k] == nums[k] * nums[k]);
    
    result
}

} // verus!