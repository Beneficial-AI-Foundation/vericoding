// <vc-preamble>
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_max(nums: Vec<i32>) -> (ret:i32)

    requires
        nums.len() > 0,

    ensures
        forall |i: int| 0 <= i < nums@.len() ==> nums@[i] <= ret,
        exists |i: int| 0 <= i < nums@.len() ==> nums@[i] == ret,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): corrected the exists loop invariant from implication (==>) to conjunction (&&) */
    let mut max = nums[0];
    let mut i: usize = 1;
    while i < nums.len()
        invariant
            nums.len() > 0,
            1 <= i <= nums.len(),
            forall|k: int| 0 <= k < (i as int) ==> nums@[k] <= max,
            exists|k: int| 0 <= k < (i as int) && nums@[k] == max,
        decreases nums.len() - i
    {
        if nums[i] > max {
            max = nums[i];
        }
        i = i + 1;
    }
    max
}
// </vc-code>

}
fn main() {}