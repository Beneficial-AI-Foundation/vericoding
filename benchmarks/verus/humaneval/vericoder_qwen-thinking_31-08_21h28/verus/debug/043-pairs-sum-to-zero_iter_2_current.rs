use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let n = nums.len();
    for i in 0..n-1 {
        //@ invariant 0 <= i < n
        //@ invariant (forall |k: int, l: int| 0 <= k < i && k < l < n ==> nums[k] + nums[l] != target)
        for j in i+1..n {
            //@ invariant i+1 <= j < n
            //@ invariant (forall |l: int| i < l < j ==> nums[i] + nums[l] != target)
            //@ invariant (forall |k: int, l: int| 0 <= k < i && k < l < n ==> nums[k] + nums[l] != target)
            if nums[i] + nums[j] == target {
                return true;
            }
        }
    }
    return false;
}
// </vc-code>

fn main() {}
}