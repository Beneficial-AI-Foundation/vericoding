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
    /* code modified by LLM (iteration 3): fixed invariant to ensure max_val is always from the visited portion */
    let mut max_val = nums[0];
    let mut i = 1;
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            forall |j: int| 0 <= j < i ==> nums@[j] <= max_val,
            exists |j: int| 0 <= j < i && nums@[j] == max_val,
        decreases nums.len() - i
    {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }
    max_val
}
// </vc-code>

}
fn main() {}