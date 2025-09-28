// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define safe_cube helper to prevent overflow */
fn safe_cube(x: i32) -> (result: i32)
    requires
        i32::MIN <= x * x <= i32::MAX,
        i32::MIN <= x * x * x <= i32::MAX,
    ensures
        result == x * x * x
{
    let square = x * x;
    square * x
}
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
/* code modified by LLM (iteration 5): fix proof by explicitly instantiating preconditions */
{
    let mut cubed = Vec::new();
    for i in 0..nums.len()
        invariant
            cubed.len() == i,
            forall|j: int| 0 <= j < i ==> cubed[j] == nums[j] * nums[j] * nums[j],
    {
        let x = nums[i];
        proof {
            let i_ghost = i as int;
            assert(0 <= i_ghost < nums.len());
            assert_by(
                i32::MIN <= nums[i_ghost] * nums[i_ghost] <= i32::MAX,
                {
                    assert(forall|k: int| 0 <= k < nums.len() ==> i32::MIN <= nums[k] * nums[k] <= i32::MAX);
                }
            );
            assert_by(
                i32::MIN <= nums[i_ghost] * nums[i_ghost] * nums[i_ghost] <= i32::MAX,
                {
                    assert(forall|k: int| 0 <= k < nums.len() ==> i32::MIN <= nums[k] * nums[k] * nums[k] <= i32::MAX);
                }
            );
        }
        let cube = safe_cube(x);
        cubed.push(cube);
    }
    cubed
}
// </vc-code>

}
fn main() {}