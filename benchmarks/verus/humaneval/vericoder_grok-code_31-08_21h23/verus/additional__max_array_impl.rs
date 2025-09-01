use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
    let mut idx: usize = 0;
    let mut i: usize = 1;
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            0 <= idx < i,
            forall|j: int| 0 <= j < i ==> #[trigger] nums[j] <= nums[idx as int],
        decreases nums.len() - i
    {
        if nums[i] > nums[idx] {
            idx = i;
        }
        i += 1;
    }
    idx
}
// </vc-code>

fn main() {}
}