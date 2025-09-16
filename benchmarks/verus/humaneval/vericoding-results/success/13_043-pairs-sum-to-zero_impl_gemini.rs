// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn pairs_sum_to_zero(nums: &[i32], target: i32) -> (found: bool)

    requires
        nums.len() >= 2,
        forall|i: int, j: int|
            0 <= i < j < nums.len() ==> nums[i] + nums[j] <= i32::MAX && nums[i] + nums[j]
                >= i32::MIN,

    ensures
        found <==> exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): cast usize variables to int for spec statements */
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall|k: int, l: int|
                0 <= k < (i as int) && k < l < (nums.len() as int) ==> nums@[k] + nums@[l] != target,
        decreases nums.len() - i
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len(),
                i + 1 <= j <= nums.len(),
                forall|k: int, l: int|
                    0 <= k < (i as int) && k < l < (nums.len() as int) ==> nums@[k] + nums@[l] != target,
                forall|l: int| (i as int) < l < (j as int) ==> nums@[i as int] + nums@[l] != target,
            decreases nums.len() - j
        {
            if nums[i] + nums[j] == target {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}