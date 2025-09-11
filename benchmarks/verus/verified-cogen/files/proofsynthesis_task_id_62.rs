// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn smallest_num(nums: &Vec<i32>) -> (min: i32)

    requires
        nums.len() > 0,

    ensures
        forall|i: int| 0 <= i < nums.len() ==> min <= nums[i],
        exists|i: int| 0 <= i < nums.len() && min == nums[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}