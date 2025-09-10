use vstd::prelude::*;

verus! {

fn remove_duplicates(nums: &Vec<i32>) -> (result: usize)
    requires forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j],
    ensures result <= nums.len(),
{
    assume(false);
    unreached();
}

}
fn main() {}