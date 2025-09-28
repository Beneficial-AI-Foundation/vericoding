use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty
// </vc-helpers>

// <vc-spec>
fn twoSum(nums: &[i32], target: i32) -> (result: (usize, usize))
    requires 
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures 
        0 <= result.0 < result.1 < nums.len() && nums[result.0 as int] + nums[result.1 as int] == target
        && forall|ii: int, jj: int| #![trigger nums[ii], nums[jj]] (0 <= ii < result.0 && ii < jj < nums.len()) ==> nums[ii] + nums[jj] != target
        && forall|jj: int| #![trigger nums[jj]] result.0 < jj < result.1 ==> nums[result.0 as int] + nums[jj] != target,
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    decreases(nums.len() - 1 - i);
    while i < nums.len() - 1
        invariant { forall |k: int| 0 <= k < i as int ==> forall |kk: int| #[trigger(nums[k], nums[kk])] k < kk < nums.len() as int ==> nums[k] + nums[kk] != target },
        invariant { exists |k: int, kk: int| #[trigger(nums[k], nums[kk])] i as int <= k < kk < nums.len() as int && nums[k] + nums[kk] == target },
    {
        let mut j: usize = i + 1;
        decreases(nums.len() - j);
        while j < nums.len()
            invariant { j >= i + 1 },
            invariant { forall |jj: int| #[trigger(nums[jj])] i as int < jj < j as int ==> nums[i as int] + nums[jj] != target },
            invariant { exists |jj: int| #[trigger(nums[jj])] j as int <= jj < nums.len() as int && nums[i as int] +
// </vc-code>

fn main() {}

}