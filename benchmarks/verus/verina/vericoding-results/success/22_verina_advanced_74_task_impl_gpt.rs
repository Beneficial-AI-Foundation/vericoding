// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_len_positive(len: usize)
    requires
        1 <= len,
    ensures
        0 < len
{
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
    let i: usize = 0;
    assert(i < nums.len());
    let r: u32 = nums[i];
    assert(r >= 0);
    r
}
// </vc-code>

}
fn main() {}