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
    /* code modified by LLM (iteration 4): Changed count to i32 and capped it to prevent arithmetic overflow. */
    let mut count: i32 = 0;
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            0 <= count <= i32::MAX,
        decreases nums.len() - i
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                i < nums.len(),
                i < j <= nums.len(),
                0 <= count <= i32::MAX,
            decreases nums.len() - j
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