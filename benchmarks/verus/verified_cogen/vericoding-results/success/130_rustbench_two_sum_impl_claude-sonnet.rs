// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_sum(nums: &[i32], target: i32) -> (result: (usize, usize))
    requires
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
        forall|i: int, j: int|
            0 <= i < nums.len() && 0 <= j < nums.len()
                ==> nums[i] + nums[j] <= i32::MAX
                    && nums[i] + nums[j] >= i32::MIN,
    ensures
        ({ let (i, j) = result; 0 <= i < nums.len() }),
        ({ let (i, j) = result; 0 <= j < nums.len() }),
        ({ let (i, j) = result; i != j }),
        ({ let (i, j) = result; nums[i as int] + nums[j as int] == target })
// </vc-spec>
// <vc-code>
{
    for i in 0..nums.len()
        invariant
            forall|k: int, l: int| 0 <= k < i && 0 <= l < nums.len() ==> nums[k] + nums[l] != target || k == l,
    {
        for j in (i + 1)..nums.len()
            invariant
                forall|k: int, l: int| 0 <= k < i && 0 <= l < nums.len() ==> nums[k] + nums[l] != target || k == l,
                forall|l: int| (i + 1) <= l < j ==> nums[i as int] + nums[l] != target,
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
        }
    }
    unreached()
}
// </vc-code>

}
fn main() {}