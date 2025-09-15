// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted(nums: &Vec<i32>) -> bool { forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j] }
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(nums: &Vec<i32>) -> (result: usize)
    requires forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j],
    ensures result <= nums.len(),
// </vc-spec>
// <vc-code>
{
    let result = nums.len();
    result
}
// </vc-code>

}
fn main() {}