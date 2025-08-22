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
    
    /* code modified by LLM (iteration 3): added decreases clause and proper precondition instantiation */
    while i < nums.len()
        invariant
            i <= nums.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == nums[k] * nums[k],
        decreases nums.len() - i,
    {
        /* code modified by LLM (iteration 3): properly instantiate precondition for current index */
        assert(0 <= i < nums.len());
        assert(0 <= nums[i as int] * nums[i as int] < i32::MAX) by {
            assert(0 <= i as int < nums.len() as int);
        }
        let squared_val = nums[i] * nums[i];
        result.push(squared_val);
        /* code modified by LLM (iteration 3): added assertion to help maintain loop invariant */
        assert(result[i as int] == nums[i as int] * nums[i as int]);
        i += 1;
    }
    
    result
}

} // verus!