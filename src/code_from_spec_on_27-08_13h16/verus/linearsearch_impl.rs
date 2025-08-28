#[allow(unused_imports)]
use vstd::prelude::*;


verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
fn linear_search(nums: Vec<i32>, target: i32) -> (ret: i32)
    // pre-conditions-start
    requires
        nums@.len() < 0x8000_0000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ret < nums@.len(),
        ret >=0 ==> nums@[ret as int] == target,
        ret >=0 ==> forall |i: int| 0 <= i < ret as int ==> #[trigger]nums@[i]!= target,
        ret < 0 ==> forall |i: int| 0 <= i < nums@.len() as int ==> #[trigger]nums@[i] != target,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    let len = nums.len();
    while i < len
        invariant
            0 <= i <= len,
            len == nums@.len(),
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums@[k] != target,
        decreases
            len - i
    {
        if nums[i] == target {
            return i as i32;
        }
        i = i + 1;
    }
    return -1;
}
// </vc-code>

}

fn main() {}