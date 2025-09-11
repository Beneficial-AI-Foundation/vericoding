// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn remove_element(nums: &mut Vec<i32>, val: i32) -> (i: usize)
    requires 
        old(nums).len() <= 100,
        forall|j: int| 0 <= j < old(nums).len() ==> #[trigger] old(nums)[j] >= 0 && old(nums)[j] <= 50,
        0 <= val <= 100,
    ensures
        forall|j: int| 0 < j < i < nums.len() ==> #[trigger] nums[j] != val,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}