// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: Vec<i32>) -> (result: usize)
    ensures
        result >= 0,
        nums.len() == 0 ==> result == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fix type annotation for dp vector */
    if nums.len() == 0 {
        return 0;
    }
    
    let mut dp: Vec<usize> = Vec::with_capacity(nums.len());
    let mut i = 0;
    
    while i < nums.len()
        invariant
            i <= nums.len(),
            dp.len() == i,
            forall|idx: int| 0 <= idx < dp.len() ==> dp[idx] >= 1,
        decreases nums.len() - i
    {
        dp.push(1);
        i += 1;
    }
    
    let mut j = 1;
    while j < nums.len()
        invariant
            j <= nums.len(),
            dp.len() == nums.len(),
            forall|idx: int| 0 <= idx < dp.len() ==> dp[idx] >= 1,
        decreases nums.len() - j
    {
        let mut k = 0;
        while k < j
            invariant
                k <= j,
                j < nums.len(),
                dp.len() == nums.len(),
                forall|idx: int| 0 <= idx < dp.len() ==> dp[idx] >= 1,
            decreases j - k
        {
            if nums[k] < nums[j] {
                let dp_k = dp[k];
                let dp_j = dp[j];
                if dp_k < usize::MAX && dp_k + 1 > dp_j {
                    dp.set(j, dp_k + 1);
                }
            }
            k += 1;
        }
        j += 1;
    }
    
    let mut max_len = 0;
    let mut idx = 0;
    while idx < dp.len()
        invariant
            idx <= dp.len(),
            max_len >= 0,
        decreases dp.len() - idx
    {
        if dp[idx] > max_len {
            max_len = dp[idx];
        }
        idx += 1;
    }
    
    max_len
}
// </vc-code>

}
fn main() {}