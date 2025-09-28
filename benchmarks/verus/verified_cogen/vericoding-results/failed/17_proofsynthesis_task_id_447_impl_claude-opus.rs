// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn cube_element(nums: &Vec<i32>) -> (cubed: Vec<i32>)

    requires
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                <= i32::MAX),
        forall|k: int|
            0 <= k < nums.len() ==> (i32::MIN <= #[trigger] nums[k] * #[trigger] nums[k]
                * #[trigger] nums[k] <= i32::MAX),

    ensures
        forall|i: int|
            0 <= i < nums.len() ==> cubed[i] == #[trigger] nums[i] * #[trigger] nums[i]
                * #[trigger] nums[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use preconditions directly without extra assertions */
    let mut cubed = Vec::new();
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            cubed.len() == i,
            forall|j: int| 0 <= j < i ==> cubed[j] == nums[j] * nums[j] * nums[j],
        decreases nums.len() - i,
    {
        let cube = nums[i] * nums[i] * nums[i];
        cubed.push(cube);
        i += 1;
    }
    cubed
}
// </vc-code>

}
fn main() {}