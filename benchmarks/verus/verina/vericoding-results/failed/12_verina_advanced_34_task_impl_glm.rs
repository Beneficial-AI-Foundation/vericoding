// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn max_i32(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        result <= nums.len() as i32,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed loop condition syntax by adding parentheses */
{
    let n = nums.len();
    if n == 0 {
        return 0;
    }
    let mut dp: Vec<i32> = Vec::new();
    dp.push(1);
    let mut i = 1;
    while (i < n)
        invariant { 1 <= i <= n }
        invariant { dp.len() == i }
        decreases n - i 
    {
        let mut current = 1;
        let mut j = 0;
        while (j < i)
            invariant { 0 <= j <= i }
            invariant { dp.len() == i }
            decreases i - j 
        {
            if nums[j] < nums[i] {
                current = max_i32(current, dp[j] + 1);
            }
            j += 1;
        }
        dp.push(current);
        i += 1;
    }
    let mut result = 0;
    for i in 0..n {
        result = max_i32(result, dp[i]);
    }
    result
}
// </vc-code>

}
fn main() {}