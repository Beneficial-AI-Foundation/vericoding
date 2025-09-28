// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding a `spec` function `i32_cube` for logical manipulation of i32 values. */
spec fn i32_cube(x: i32) -> i32 {
    (x as int * x as int * x as int) as i32
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
/* code modified by LLM (iteration 5): Replaced direct `int` casts in operational code with a call to the `i32_cube` spec function for proper type handling. */
{
    let mut cubed = Vec::new();
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            cubed.len() == i,
            forall|k: int| 0 <= k < i ==> cubed[k] == i32_cube(nums[k]),
        decreases nums.len() - i
    {
        let val: i32 = nums[i];
        let cubed_val: i32 = i32_cube(val);
        cubed.push(cubed_val);
        i = i + 1;
    }
    cubed
}
// </vc-code>

}
fn main() {}