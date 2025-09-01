use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let n = nums.len();
    let mut max_idx = 0;
    let mut i = 1;
    while i < n
        invariant
            i <= n,
            0 <= max_idx < i,
            forall |j: int| 0 <= j < (i as int) ==> #[trigger] nums[j] <= nums[max_idx as int],
    {
        if nums[i] > nums[max_idx] {
            max_idx = i;
        }
        i = i + 1;
    }
    max_idx
}
// </vc-code>

fn main() {}
}