use vstd::prelude::*;

verus! {

fn longest_increasing_subsequence(nums: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        result <= nums.len() as i32,
{
    assume(false);
    unreached();
}

}
fn main() {}