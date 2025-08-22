use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn pairs_sum_to_zero(nums: &[i32], target: i32) -> (found: bool)
    // pre-conditions-start
    requires
        nums.len() >= 2,
        forall|i: int, j: int|
            0 <= i < j < nums.len() ==> nums[i] + nums[j] <= i32::MAX && nums[i] + nums[j]
                >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        found <==> exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    // post-conditions-end
{
    let mut i: usize = 0;
    while i < nums.len() - 1
        invariant
            0 <= i <= nums.len() - 1,
            forall|ii: int, jj: int| 0 <= ii < i && ii < jj < nums.len() ==> nums[ii] + nums[jj] != target,
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len() - 1,
                i + 1 <= j <= nums.len(),
                forall|ii: int, jj: int| 0 <= ii < i && ii < jj < nums.len() ==> nums[ii] + nums[jj] != target,
                forall|jj: int| i < jj < j ==> nums[i] + nums[jj] != target,
        {
            if nums[i] + nums[j] == target {
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    false
}

}
fn main() {}