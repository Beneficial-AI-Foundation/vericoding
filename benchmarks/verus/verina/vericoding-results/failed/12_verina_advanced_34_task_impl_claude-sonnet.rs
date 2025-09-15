// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified helper to avoid complex quantifier issues */
spec fn is_valid_dp_entry(val: i32) -> bool {
    val >= 1
}

spec fn is_valid_length(len: i32, max_len: usize) -> bool {
    len >= 0 && len <= max_len as i32
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
    /* code modified by LLM (iteration 5): fixed bounds checking and cast issues */
    if nums.len() == 0 {
        return 0;
    }
    
    let mut dp = Vec::new();
    let mut i = 0;
    while i < nums.len()
        invariant i <= nums.len(), dp.len() == i
        decreases nums.len() - i
    {
        dp.push(1);
        i += 1;
    }
    
    let mut max_length = 1i32;
    let mut i = 1;
    while i < nums.len()
        invariant 
            1 <= i <= nums.len(), 
            dp.len() == nums.len(),
            max_length >= 1,
            max_length <= nums.len() as i32
        decreases nums.len() - i
    {
        let mut j = 0;
        while j < i
            invariant 
                j <= i,
                i < nums.len(),
                dp.len() == nums.len()
            decreases i - j
        {
            if nums[j] < nums[i] {
                let temp_val = dp[j] + 1;
                if temp_val > dp[i] {
                    dp.set(i, temp_val);
                }
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