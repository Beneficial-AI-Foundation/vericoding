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
    let mut max_index: usize = 0;
    let mut i: usize = 1;
    while i < nums.len() {
        invariant {
            0 <= max_index && max_index < i &&
            forall |j: int| (0 <= j && j < (i as int)) ==> nums[j as usize] <= nums[max_index]
        }
        if nums[i] > nums[max_index] {
            max_index = i;
        }
        i += 1;
    }
    max_index
}
// </vc-code>

fn main() {}
}