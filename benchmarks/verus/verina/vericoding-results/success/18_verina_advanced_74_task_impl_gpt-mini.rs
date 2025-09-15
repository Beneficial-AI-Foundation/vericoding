// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): returns first element of a non-empty vector */
fn first_elem(nums: Vec<u32>) -> u32
    requires
        nums.len() >= 1,
{
    nums[0]
}
// </vc-helpers>

// <vc-spec>
fn solution(nums: Vec<u32>) -> (result: u32)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] >= 1 && #[trigger] nums[i] <= 100,
    ensures
        result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): return first element using helper */
    let result: u32 = first_elem(nums);
    result
}
// </vc-code>

}
fn main() {}