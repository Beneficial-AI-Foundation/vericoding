use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_sum(nums: &[i32], target: i32) -> (result: (usize, usize))
    // pre-conditions-start
    requires
        nums.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
        forall|i: int, j: int|
            0 <= i < nums.len() && 0 <= j < nums.len()
                ==> nums[i] + nums[j] <= i32::MAX
                    && nums[i] + nums[j] >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ({ let (i, j) = result; 0 <= i < nums.len() }),
        ({ let (i, j) = result; 0 <= j < nums.len() }),
        ({ let (i, j) = result; i != j }),
        ({ let (i, j) = result; nums[i as int] + nums[j as int] == target })
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = nums.len();
    for i in 0..n
        invariant
            0 <= i <= n,
            forall|k: int, l: int| 0 <= k < i as int && k < l < n as int ==> nums@[k] + nums@[l] != target,
    {
        for j in (i+1)..n
            invariant
                i+1 <= j <= n,
                forall|l: int| (i+1) as int <= l < j as int ==> nums@[i as int] + nums@[l] != target,
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
        }
    }
    assert(false);
    return (0, 0);
}
// </vc-code>

fn main() {}
}