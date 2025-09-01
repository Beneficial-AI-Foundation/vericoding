use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helper functions needed for this proof.
// </vc-helpers>

// <vc-spec>
fn max_array(nums: &[i32]) -> (idx: usize)
    // pre-conditions-start
    requires
        nums.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= idx && idx < nums.len(),
        forall|i: int| 0 <= i && i < nums.len() ==> nums[i] <= nums[idx as int],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n: usize = nums.len();
    let mut max_idx: usize = 0;
    let mut i: usize = 1usize;
    while i < n
        invariant
            1usize <= n,
            i <= n,
            max_idx < n,
            forall|j: int| 0 <= j && j < i as int ==> nums[j as usize] <= nums[max_idx],
    {
        if nums[i] > nums[max_idx] {
            let old: usize = max_idx;
            // remember the relation before updating
            assert(nums[i] > nums[old]);
            max_idx = i;
            // need to establish invariant for j < i+1 with new max_idx
            // For j < i: nums[j] <= nums[old] and nums[old] < nums[i] imply nums[j] < nums[i] <= nums[max_idx]
            // For j == i: nums[i] <= nums[max_idx] holds trivially
            assert(forall|j: int| 0 <= j && j < i as int ==>
                nums[j as usize] <= nums[max_idx]);
            assert(nums[i] <= nums[max_idx]);
            assert(forall|j: int| 0 <= j && j < (i as int) + 1 ==> nums[j as usize] <= nums[max_idx]);
        } else {
            // max_idx unchanged; need to show property holds for j < i+1
            // For j < i it holds by invariant; for j == i it holds by branch condition
            assert(nums[i] <= nums[max_idx]);
            assert(forall|j: int| 0 <= j && j < (i as int) + 1 ==> nums[j as usize] <= nums[max_idx]);
        }
        i = i + 1;
    }
    // after loop, i == n and invariant gives property for all j < n
    max_idx
    // impl-end
}
// </vc-code>

fn main() {}
}