// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec cube on int */
spec fn cube_int(x: int) -> int { x * x * x }
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
    /* code modified by LLM (iteration 5): compute cubes using int intermediates and prove casts safe */
    let mut cubed = Vec::<i32>::new();
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            cubed.len() == i,
            forall|k: int|
                0 <= k < i as int ==> (cubed@[k] as int) == cube_int(nums@[k] as int),
        decreases nums.len() - i
    {
        let x: i32 = nums[i];
        let xi: int = x as int;
        let c_int: int = cube_int(xi);
        proof {
            assert(0 <= i as int);
            assert((i as int) < (nums.len() as int));
            assert((nums@[i as int] as int) == xi);
            assert(i32::MIN as int <= (nums@[i as int] as int) * (nums@[i as int] as int) * (nums@[i as int] as int));
            assert((nums@[i as int] as int) * (nums@[i as int] as int) * (nums@[i as int] as int) <= i32::MAX as int);
            assert(c_int == (nums@[i as int] as int) * (nums@[i as int] as int) * (nums@[i as int] as int));
        }
        let c_i32: i32 = c_int as i32;
        cubed.push(c_i32);
        i = i + 1;
    }
    cubed
}
// </vc-code>

}
fn main() {}