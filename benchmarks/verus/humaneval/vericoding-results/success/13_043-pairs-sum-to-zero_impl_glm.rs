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
/* code modified by LLM (iteration 3): fixed slice indexing in invariants using @ operator */
{
    let n = nums.len();
    let mut i: usize = 0;
    let mut j: usize;
    let mut found = false;
    while i < n - 1
        invariant
            i as int >= 0,
            i as int <= (n - 1) as int,
            found <==> exists|i0: int, j0: int|
                0 <= i0 < i as int && i0 < j0 && j0 < n as int && nums@[i0] + nums@[j0] == target,
        decreases (n as int) - (i as int)
    {
        j = i + 1;
        while j < n
            invariant
                (i as int) + 1 <= j as int,
                j as int <= n as int,
                found <==> exists|i0: int, j0: int|
                    (0 <= i0 < i as int && i0 < j0 < n as int && nums@[i0] + nums@[j0] == target) ||
                    (i0 == i as int && (i as int)+1 <= j0 < j as int && nums@[i0] + nums@[j0] == target),
            decreases (n as int) - (j as int)
        {
            if nums[i] + nums[j] == target {
                found = true;
                break;
            }
            j += 1;
        }
        if found {
            break;
        }
        i += 1;
    }
    found
}
// </vc-code>

}
fn main() {}