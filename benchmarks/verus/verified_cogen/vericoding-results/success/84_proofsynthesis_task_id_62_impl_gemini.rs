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
    /* code modified by LLM (iteration 5): add decreases clause to prove loop termination */
    let mut min = nums[0];
    let mut i: usize = 1;
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            forall|j: int| 0 <= j < i ==> min <= nums@[j],
            exists|j: int| 0 <= j < i && min == nums@[j],
        decreases nums.len() - i
    {
        if nums[i] < min {
            min = nums[i];
        }
        i = i + 1;
    }
    min
}
// </vc-code>

}
fn main() {}