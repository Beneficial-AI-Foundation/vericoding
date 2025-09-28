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
    /* code modified by LLM (iteration 4): moved ghost code into a proof block and fixed invariant syntax */
    let mut cubed: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            cubed.len() == i,
            forall|k: int| 0 <= k < i ==> cubed@.index(k) as int == (nums@.index(k) as int) * (nums@.index(k) as int) * (nums@.index(k) as int),
        decreases nums.len() - i,
    {
        let val = nums[i];

        proof {
            let val_int = val as int;
            assert(i32::MIN <= val_int * val_int <= i32::MAX);
            assert(i32::MIN <= val_int * val_int * val_int <= i32::MAX);
        }

        let c = val * val * val;
        cubed.push(c);
        i = i + 1;
    }
    cubed
}
// </vc-code>

}
fn main() {}