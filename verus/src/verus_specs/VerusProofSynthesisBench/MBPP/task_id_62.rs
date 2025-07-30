use vstd::prelude::*;


verus! {

fn smallest_num(nums: &Vec<i32>) -> (min: i32)
    // pre-conditions-start
    requires
        nums.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| 0 <= i < nums.len() ==> min <= nums[i],
        exists|i: int| 0 <= i < nums.len() && min == nums[i],
    // post-conditions-end
{
    return 0;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
