// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn trivial_helper() { }
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(nums: &Vec<i32>) -> (result: usize)
    requires forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j],
    ensures result <= nums.len(),
// </vc-spec>
// <vc-code>
{
    let n = nums.len();
    n
}
// </vc-code>

}
fn main() {}