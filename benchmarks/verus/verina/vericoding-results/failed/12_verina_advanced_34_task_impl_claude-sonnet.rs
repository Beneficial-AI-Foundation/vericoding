// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// Helper function to check if a subsequence is increasing
spec fn is_increasing_subseq(nums: Seq<i32>, indices: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < indices.len() - 1 ==> #[trigger] (indices[i] < indices[i + 1] &&
        indices[i + 1] < nums.len() &&
        nums[indices[i] as int] < nums[indices[i + 1] as int])
}

/* helper modified by LLM (iteration 5): fixed syntax error in forall quantifier */
// Helper function to get length of longest increasing subsequence ending at position i
fn lis_ending_at(nums: &Vec<i32>, pos: usize) -> (result: usize)
    requires
        pos < nums.len(),
    ensures
        result >= 1,
        result <= pos + 1,
    decreases pos
{
    let mut max_len = 1;
    let mut j = 0;
    
    while j < pos
        invariant
            j <= pos,
            max_len >= 1,
            max_len <= pos + 1,
        decreases pos - j
    {
        if nums[j] < nums[pos] {
            let len_at_j = lis_ending_at(nums, j);
            if len_at_j + 1 > max_len {
                max_len = len_at_j + 1;
            }
        }
        j += 1;
    }
    
    max_len
}
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        result <= nums.len() as i32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed for main function */
    if nums.len() == 0 {
        return 0;
    }
    
    let mut max_length = 1i32;
    let mut i = 0;
    
    while i < nums.len()
        invariant
            i <= nums.len(),
            max_length >= 1,
            max_length <= nums.len() as i32,
        decreases nums.len() - i
    {
        let len_at_i = lis_ending_at(nums, i);
        if len_at_i as i32 > max_length {
            max_length = len_at_i as i32;
        }
        i += 1;
    }
    
    max_length
}
// </vc-code>

}
fn main() {}