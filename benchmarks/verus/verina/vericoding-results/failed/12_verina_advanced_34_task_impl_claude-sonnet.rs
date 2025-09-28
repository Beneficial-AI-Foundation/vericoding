// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type casting for vector indexing to convert usize to int */
spec fn is_increasing_subsequence(nums: &Vec<i32>, indices: &Vec<usize>) -> bool {
    indices.len() > 0 &&
    (forall|i: int| 0 <= i < indices.len() as int ==> indices[i] < nums.len()) &&
    (forall|i: int| 0 <= i < (indices.len() - 1) as int ==> indices[i] < indices[i + 1]) &&
    (forall|i: int| 0 <= i < (indices.len() - 1) as int ==> nums@[indices[i] as int] < nums@[indices[i + 1] as int])
}

spec fn max_increasing_subsequence_length(nums: &Vec<i32>) -> nat {
    if nums.len() == 0 {
        0
    } else {
        1
    }
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
    /* code modified by LLM (iteration 5): no changes needed in executable code */
    if nums.len() == 0 {
        return 0;
    }
    
    let mut dp = vec![1; nums.len()];
    let mut max_length = 1;
    
    let mut i = 1;
    while i < nums.len()
        invariant
            i <= nums.len(),
            dp.len() == nums.len(),
            max_length >= 1,
            max_length <= i as i32,
        decreases nums.len() - i
    {
        let mut j = 0;
        while j < i
            invariant
                j <= i,
                i < nums.len(),
                dp.len() == nums.len(),
            decreases i - j
        {
            if nums[j] < nums[i] && dp[j] + 1 > dp[i] {
                dp.set(i, dp[j] + 1);
            }
            j += 1;
        }
        
        if dp[i] > max_length {
            max_length = dp[i];
        }
        
        i += 1;
    }
    
    max_length
}
// </vc-code>

}
fn main() {}