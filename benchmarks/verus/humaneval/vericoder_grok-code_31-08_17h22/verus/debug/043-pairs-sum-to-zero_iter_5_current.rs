use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
    let len = nums.len();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= (i as int) <= len as int,
            forall |a: int, b: int| 0 <= a < b < (i as int) ==> #[trigger] nums@[a] + nums@[b] == target,
        {
            let mut j: usize = i + 1;
            while j < len
                invariant
                    (i as int) < (j as int) <= len as int,
                    forall |b: int| (i as int) < b < (j as int) ==> #[trigger] nums@[i as int] + nums@[b] == target,
                {
                    if nums[i] + nums[j] == target {
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