use vstd::prelude::*;

verus! {

// <vc-helpers>
// no changes needed
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn pairs_sum_to_zero(nums: &[i32], target: i32) -> (found: bool)
    // pre-conditions-start
    requires
        nums.len() >= 2,
        forall|i: int, j: int|
            0 <= i < j < nums.len() ==> nums[i] + nums[j] <= i32::MAX && nums[i] + nums[j]
                >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        found <==> exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let len = nums.view().len();
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            forall |a: int, b: int| 0 <= a < b < i ==> #[trigger] nums@[a] + nums@[b] == target,
        {
            let mut j = i + 1;
            while j < len
                invariant
                    i < j <= len,
                    forall |b: int| i < b < j ==> #[trigger] nums@[i] + nums@[b] == target,
                {
                    if nums@[i] + nums@[j] == target {
                        return true;
                    }
                    j += 1;
                }
            i += 1;
        }
    return false;
}
// </vc-code>

fn main() {}
}