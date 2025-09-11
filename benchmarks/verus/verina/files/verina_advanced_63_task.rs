// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(nums: &Vec<i32>) -> (result: usize)
    requires forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j],
    ensures result <= nums.len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}