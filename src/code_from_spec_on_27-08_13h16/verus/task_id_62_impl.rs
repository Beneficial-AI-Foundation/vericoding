use vstd::prelude::*;


verus! {

// <vc-helpers>
fn find_min_helper(nums: &Vec<i32>, i: usize, current_min: i32) -> (min: i32)
    requires
        0 < i <= nums.len(),
        forall|k: int| 0 <= k < i as int ==> current_min <= nums[k],
        exists|k: int| 0 <= k < i as int && current_min == nums[k],
    ensures
        forall|k: int| 0 <= k < nums.len() ==> min <= nums[k],
        exists|k: int| 0 <= k < nums.len() && min == nums[k],
    decreases nums.len() - i
{
    if i == nums.len() {
        current_min
    } else {
        let new_min = if nums[i] < current_min { nums[i] } else { current_min };
        find_min_helper(nums, i + 1, new_min)
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    find_min_helper(nums, 1, nums[0])
}
// </vc-code>

} // verus!

fn main() {}