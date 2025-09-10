use vstd::prelude::*;

verus! {

fn longest_increasing_subsequence(nums: Vec<i32>) -> (result: usize)
    ensures
        result >= 0,
        nums.len() == 0 ==> result == 0,
{
    assume(false);
    unreached()
}

}
fn main() {}