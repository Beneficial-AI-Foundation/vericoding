// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): returns the greater of two u32 numbers */
fn max_u32(a: u32, b: u32) -> u32 { if a > b { a } else { b } }
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
    /* code modified by LLM (iteration 2): compute maximum element of nums */
    let mut i: usize = 0;
    let mut res: u32 = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
        decreases nums.len() - i
    {
        let v: u32 = nums[i];
        if v > res {
            res = v;
        }
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}