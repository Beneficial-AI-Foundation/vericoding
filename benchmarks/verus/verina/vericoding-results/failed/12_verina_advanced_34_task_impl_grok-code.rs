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
/* code modified by LLM (iteration 4): added decreases clauses for all while loops to ensure termination */
{
    if nums.len() == 0 {
        return 0;
    }
    let mut dp: Vec<i32> = Vec::with_capacity(nums.len());
    let mut i: usize = 0;
    while i < nums.len()
        invariant
          i <= nums.view().len(),
          dp.view().len() == i as int,
        decreases nums.len() - i
    {
        dp.push(1);
        let mut j: usize = 0;
        while j < i
            invariant
                j <= i,
            decreases i - j
        {
            if nums[j] < nums[i] {
                let new_len = dp[j] + 1;
                if new_len > dp[i] {
                    dp[i] = new_len;
                }
            }
            j += 1;
        }
        i += 1;
    }
    let mut max_len: i32 = 0;
    let mut idx: usize = 0;
    while idx < dp.len()
        invariant
          idx <= dp.view().len(),
          max_len >= 0,
          forall |k: int| 0 <= k < idx ==> dp.view()[k] <= max_len,
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