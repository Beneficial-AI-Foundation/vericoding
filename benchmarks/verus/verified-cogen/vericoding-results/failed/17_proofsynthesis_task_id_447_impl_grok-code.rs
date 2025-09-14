// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Same as previous, no helpers needed currently as function is self-contained */
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
/* code modified by LLM (iteration 5): Removed proof assertion splits as they caused verification failure due to trigger issues; added #![auto] to loop invariant forall to fix triggering issues */
    let mut cubed: Vec<i32> = Vec::new();
    let len = nums.len();
    for i in 0..len
        invariant
            cubed.len() as int == i as int,
            forall|j: int| #![auto] (0 <= j < i as int ==> cubed@[j] == nums@[j] * nums@[j] * nums@[j])
    {
        let x = nums[i];
        let sq = x * x;
        let cube = sq * x;
        cubed.push(cube);
    }
    cubed
}
// </vc-code>

}
fn main() {}