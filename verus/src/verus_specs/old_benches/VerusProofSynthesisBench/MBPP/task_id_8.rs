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
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
