// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        result <= nums.len() as i32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed cast issues and invariants */
    if nums.len() == 0 {
        return 0;
    }
    
    let n = nums.len() as i32;
    let mut dp = Vec::new();
    dp.push(1i32);
    
    let mut i: usize = 1;
    while i < nums.len()
        invariant
            dp.len() == i,
            i <= nums.len(),
            forall|k: int| 0 <= k < dp.len() ==> dp@[k] >= 1,
            forall|k: int| 0 <= k < dp.len() ==> dp@[k] <= n,
        decreases nums.len() - i
    {
        let mut max_len: i32 = 1;
        let mut j: usize = 0;
        while j < i
            invariant
                j <= i,
                i < nums.len(),
                dp.len() == i,
                max_len >= 1,
                max_len <= n,
                forall|k: int| 0 <= k < dp.len() ==> dp@[k] >= 1,
                forall|k: int| 0 <= k < dp.len() ==> dp@[k] <= n,
            decreases i - j
        {
            if nums[j] < nums[i] {
                if dp[j] < i32::MAX {
                    let new_len = dp[j] + 1;
                    if new_len > max_len && new_len <= n {
                        max_len = new_len;
                    }
                }
            }
            j = j + 1;
        }
        dp.push(max_len);
        i = i + 1;
    }
    
    let mut result: i32 = 0;
    let mut k: usize = 0;
    while k < dp.len()
        invariant
            k <= dp.len(),
            dp.len() == nums.len(),
            result >= 0,
            result <= n,
            forall|j: int| 0 <= j < k ==> result >= dp@[j],
            forall|j: int| 0 <= j < dp.len() ==> dp@[j] >= 1,
            forall|j: int| 0 <= j < dp.len() ==> dp@[j] <= n,
        decreases dp.len() - k
    {
        if dp[k] > result {
            result = dp[k];
        }
        k = k + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}