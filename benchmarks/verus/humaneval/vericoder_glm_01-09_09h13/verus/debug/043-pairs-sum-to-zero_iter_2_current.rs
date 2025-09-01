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
    let i = 0;
    let mut found = false;
    
    while i < n
        invariant
            0 <= i <= n,
            found <==> exists|a: int, b: int| 0 <= a < b < i && nums[a] + nums[b] == target,
    {
        let j = i + 1;
        while j < n
            invariant
                i <= j,
                j <= n,
                found <==> exists|a: int, b: int| 
                    (0 <= a < b < i && nums[a] + nums[b] == target) || 
                    (a == i && i < b < j && nums[a] + nums[b] == target),
        {
            if nums[i] + nums[j] == target {
                found = true;
                proof {
                    assert(exists|a: int, b: int| 
                        (0 <= a < b < i && nums[a] + nums[b] == target) || 
                        (a == i && i < b < (j+1) && nums[a] + nums[b] == target));
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    found
}
// </vc-code>

fn main() {}
}