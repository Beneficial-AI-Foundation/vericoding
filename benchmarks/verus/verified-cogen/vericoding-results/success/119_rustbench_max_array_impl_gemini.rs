// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_max_in_slice_prefix(nums: Seq<i32>, idx: int, k: int) -> bool { forall|i: int| 0 <= i < k ==> nums[i] <= nums[idx] }
// </vc-helpers>

// <vc-spec>
fn max_array(nums: &[i32]) -> (idx: usize)
    requires
        nums.len() >= 1,
    ensures
        0 <= idx && idx < nums.len(),
        forall|i: int| 0 <= i && i < nums.len() ==> nums[i] <= nums[idx as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to the while loop */
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    while i < nums.len()
        invariant
            1 <= i && i <= nums.len(),
            0 <= max_idx && max_idx < i,
            is_max_in_slice_prefix(nums.view(), max_idx as int, i as int),
        decreases nums.len() - i
    {
        if nums[i] > nums[max_idx] {
            max_idx = i;
        }
        i = i + 1;
    }
    max_idx
}
// </vc-code>

}
fn main() {}