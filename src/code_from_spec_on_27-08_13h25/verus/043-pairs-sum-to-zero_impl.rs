use vstd::prelude::*;

verus! {

// <vc-helpers>
fn has_pair_with_sum(nums: &[i32], target: i32) -> (res: bool)
    ensures
        res <==> exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
{
    let mut i: usize = 0;
    while i < nums.len() - 1
        invariant
            0 <= i < nums.len(),
            forall|k: int, l: int| 0 <= k < l <= i ==> nums[k] + nums[l] != target,
        decreases
            nums.len() - 1 - i,
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                0 <= i < j <= nums.len(),
                forall|k: usize| i <= k < j ==> nums[i as int] + nums[k as int] != target,
                forall|k: int, l: int| 0 <= k < l <= i ==> nums[k] + nums[l] != target,
            decreases
                nums.len() - j,
        {
            if nums[i] + nums[j] == target {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    has_pair_with_sum(nums, target)
}
// </vc-code>

}
fn main() {}