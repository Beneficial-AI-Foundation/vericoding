// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn square_nums(nums: &Vec<i32>) -> (squared: Vec<i32>)

    requires
        forall|k: int|
            0 <= k < nums.len() ==> (0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX),

    ensures
        nums.len() == squared.len(),
        forall|k: int| 0 <= k < nums.len() ==> (#[trigger] squared[k] == nums[k] * nums[k]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed trigger annotation in invariant */
    let mut squared = Vec::new();
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            squared.len() == i,
            forall|k: int| 0 <= k < i ==> squared[k] == nums[k] * nums[k],
            forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] * #[trigger] nums[k] < i32::MAX,
        decreases nums.len() - i
    {
        let val = nums[i];
        squared.push(val * val);
        i += 1;
    }
    squared
}
// </vc-code>

}
fn main() {}