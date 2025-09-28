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
/* code modified by LLM (iteration 2): fixed usize suffix and implemented logic for counting distinct elements */
{
    let mut i: usize = 0;
    let mut count: usize = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            count <= i
        decreases nums.len() - i
    {
        if i == 0 || nums[i] != nums[i - 1] {
            count += 1;
        }
        i += 1;
    }
    count
}
// </vc-code>

}
fn main() {}