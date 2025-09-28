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
    /* code modified by LLM (iteration 3): fixed initial invariant by starting loop at index 1 */
    let mut min = nums[0];
    let mut idx = 1;
    
    while idx < nums.len()
        invariant
            1 <= idx <= nums.len(),
            forall|i: int| 0 <= i < idx ==> min <= nums[i],
            exists|i: int| 0 <= i < idx && min == nums[i],
        decreases nums.len() - idx
    {
        if nums[idx] < min {
            min = nums[idx];
        }
        idx += 1;
    }
    
    min
}
// </vc-code>

}
fn main() {}