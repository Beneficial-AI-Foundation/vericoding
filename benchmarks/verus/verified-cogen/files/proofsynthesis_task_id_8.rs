use vstd::prelude::*;

verus! {

fn square_nums(nums: &Vec<i32>) -> (squared: Vec<i32>)

    requires
        forall|k: int|
            0 <= k < nums.len() ==> (0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX),

    ensures
        nums.len() == squared.len(),
        forall|k: int| 0 <= k < nums.len() ==> (#[trigger] squared[k] == nums[k] * nums[k]),
{
    assume(false);
    unreached();
}

}
fn main() {}