// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn semi_ordered_permutation(nums: &Vec<i32>) -> (result: i32)
    ensures 
        result >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): add invariant to link `len` to `nums.len()` for index proofs */
    let mut count: i32 = 0;
    let len = nums.len();
    let mut i: usize = 0;
    while i < len
        invariant
            nums.len() == len,
            0 <= i <= len,
            count >= 0,
        decreases len - i
    {
        let mut j: usize = i + 1;
        while j < len
            invariant
                nums.len() == len,
                i < len,
                i + 1 <= j <= len,
                count >= 0,
            decreases len - j
        {
            if nums[i] > nums[j] {
                if count < i32::MAX {
                    count = count + 1;
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>

}
fn main() {}