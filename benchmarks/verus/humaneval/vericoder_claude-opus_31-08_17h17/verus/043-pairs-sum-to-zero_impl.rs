use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    for i in 0..n
        invariant
            forall|a: int, b: int| 
                0 <= a < i && a < b < n ==> nums[a] + nums[b] != target,
    {
        for j in (i + 1)..n
            invariant
                i < n,
                forall|a: int, b: int| 
                    0 <= a < i && a < b < n ==> nums[a] + nums[b] != target,
                forall|b: int|
                    i < b < j ==> nums[i as int] + nums[b] != target,
        {
            if nums[i] + nums[j] == target {
                assert(0 <= i < j < n);
                assert(nums[i as int] + nums[j as int] == target);
                return true;
            }
        }
    }
    
    assert(forall|a: int, b: int| 
        0 <= a < b < n ==> nums[a] + nums[b] != target);
    false
}
// </vc-code>

fn main() {}
}