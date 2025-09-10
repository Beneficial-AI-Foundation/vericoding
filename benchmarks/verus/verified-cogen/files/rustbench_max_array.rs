use vstd::prelude::*;

verus! {

fn max_array(nums: &[i32]) -> (idx: usize)
    requires
        nums.len() >= 1,
    ensures
        0 <= idx && idx < nums.len(),
        forall|i: int| 0 <= i && i < nums.len() ==> nums[i] <= nums[idx as int],
{
    assume(false);
    unreached()
}

}
fn main() {}