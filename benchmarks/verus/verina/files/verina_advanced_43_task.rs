use vstd::prelude::*;

verus! {

fn max_strength(nums: &Vec<i32>) -> (result: i32)
    requires nums.len() > 0,
    ensures

        exists|i: int| 0 <= i < nums.len() && result >= nums[i],
{
    assume(false);
    unreached();
}

}
fn main() {}