use vstd::prelude::*;

verus! {

//IMPL square_nums
/* code modified by LLM (iteration 3): Fixed function structure by properly placing requires/ensures clauses and implementing correct function body */
fn square_nums(nums: &Vec<i32>) -> (squared: Vec<i32>)
    requires
        forall|k: int|
            0 <= k < nums.len() ==> (0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX),
    ensures
        nums.len() == squared.len(),
        forall|k: int| 0 <= k < nums.len() ==> (#[trigger] squared[k] == nums[k] * nums[k]),
{
    /* code modified by LLM (iteration 4): Added decreases clause to prove loop termination */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < nums.len()
        invariant
            i <= nums.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> (#[trigger] result[k] == nums[k] * nums[k]),
        decreases nums.len() - i,
    {
        let square = nums[i] * nums[i];
        result.push(square);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}