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
    let mut max_idx: usize = 0;
    let mut max_val: i32 = nums[0];
    let mut i: usize = 1;
    let len = nums.len();
    assert(len >= 1);
    loop
        invariant
            1 <= i <= len,
            max_idx < i,
            forall |k: int| 0 <= k < i ==> nums[k as int] <= max_val,
            max_val == nums[max_idx as int],
        decreases
            (len - i as int),
    {
        if i >= len {
            break;
        }
        if nums[i] > max_val {
            max_val = nums[i];
            max_idx = i;
        }
        i = add(i, 1);
    }
    max_idx
}
// </vc-code>

fn main() {}
}