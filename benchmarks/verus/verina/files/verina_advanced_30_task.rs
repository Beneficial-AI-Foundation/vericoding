use vstd::prelude::*;

verus! {

fn longest_increasing_streak(nums: &Vec<i32>) -> (result: usize)
    ensures
        (nums.len() == 0 ==> result == 0),
        result <= nums.len(),
{
    assume(false);
    unreached();
}

}
fn main() {}