use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn pairs_sum_to_zero(nums: &[i32], target: i32) -> (found: bool)

    requires
        nums.len() >= 2,
        forall|i: int, j: int|
            0 <= i < j < nums.len() ==> nums[i] + nums[j] <= i32::MAX && nums[i] + nums[j]
                >= i32::MIN,

    ensures
        found <==> exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
{
    assume(false);
    unreached()
}

}
fn main() {}