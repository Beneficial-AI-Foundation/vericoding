#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
fn find_max(nums: Vec<i32>) -> (ret:i32)
    // pre-conditions-start
    requires
        nums.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall |i: int| 0 <= i < nums@.len() ==> nums@[i] <= ret,
        exists |i: int| 0 <= i < nums@.len() ==> nums@[i] == ret,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut max = nums[0];
    let mut i: usize = 1;
    
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            forall |j: int| 0 <= j < i ==> nums@[j] <= max,
            exists |j: int| 0 <= j < i && nums@[j] == max,
        decreases nums.len() - i
    {
        if nums[i] > max {
            max = nums[i];
        }
        i = i + 1;
    }
    
    max
}
// </vc-code>

}

fn main() {}