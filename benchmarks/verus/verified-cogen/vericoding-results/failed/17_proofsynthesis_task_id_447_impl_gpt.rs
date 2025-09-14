// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): provide spec cube and safe i32 cube helper */
spec fn cube_int(x: int) -> int { x * x * x }
fn cube_i32(x: i32) -> (r: i32)
    requires
        i32::MIN <= x * x <= i32::MAX,
        i32::MIN <= x * x * x <= i32::MAX,
    ensures
        r == x * x * x
{
    x * x * x
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
{
    /* code modified by LLM (iteration 4): removed exec int variables; use proof blocks for int casts and bounds, and compute cubes via helper */
    let n = nums.len();
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == i,
            i <= n,
            n == nums.len(),
            forall|j: int| 0 <= j < i as int ==> res[j] == nums[j] * nums[j] * nums[j]
    {
        proof {
            let i_int: int = i as int;
            assert(0 <= i_int && i_int < nums.len());
            assert(i32::MIN <= nums[i_int] * nums[i_int] <= i32::MAX);
            assert(i32::MIN <= nums[i_int] * nums[i_int] * nums[i_int] <= i32::MAX);
        }
        let x = nums[i];
        proof {
            let i_int: int = i as int;
            assert(x == nums[i_int]);
            assert(i32::MIN <= x * x <= i32::MAX);
            assert(i32::MIN <= x * x * x <= i32::MAX);
        }
        let c = cube_i32(x);
        res.push(c);
        proof {
            let i_int: int = i as int;
            assert(res.len() == i + 1);
            assert(res[i_int] == c);
            assert(res[i_int] == nums[i_int] * nums[i_int] * nums[i_int]);
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}