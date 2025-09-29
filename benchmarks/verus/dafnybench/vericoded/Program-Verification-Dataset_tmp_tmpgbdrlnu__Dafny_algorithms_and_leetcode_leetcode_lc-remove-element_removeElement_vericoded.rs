// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn removeElement(nums: &mut Vec<i32>, val: i32) -> (i: usize)
    ensures forall|k: int| 0 < k < i && k < nums.len() ==> nums[k] != val,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix compilation error by using Vec indexing `nums[j]` instead of `nums@[j]` */
    let mut i: usize = 0;
    let mut j: usize = 0;
    while j < nums.len()
        invariant
            0 <= i,
            i <= j,
            j <= nums.len(),
            forall|k: int| 0 <= k < i ==> nums@[k] != val,
        decreases nums.len() - j
    {
        if nums[j] != val {
            nums.set(i, nums[j]);
            i = i + 1;
        }
        j = j + 1;
    }
    i
}
// </vc-code>

}
fn main() {}