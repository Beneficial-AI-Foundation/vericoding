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
    if nums.len() == 0 {
        return 0;
    }
    let mut count = 1;
    let mut i = 1;
    while i < nums.len()
        invariant
            count <= i,
            1 <= i <= nums.len(),
        decreases nums.len() - i
    {
        if nums[i] != nums[i-1] {
            count += 1;
        }
        i += 1;
    }
    count
}
// </vc-code>

}
fn main() {}