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
/* code modified by LLM (iteration 4): added decreases clause to ensure loop termination */
{
    let mut result: usize = 0;
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            result <= i,
        decreases (nums.len() - i) as nat,
    {
        if i == 0 || nums[i] != nums[i - 1] {
            result += 1;
        }
        proof {
            
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}