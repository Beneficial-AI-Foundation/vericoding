// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `max` function is a helper function that returns the larger of two `i32` values. */
fn max(a: i32, b: i32) -> i32 {
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
/* code modified by LLM (iteration 5): The main task for `longest_increasing_subsequence` is to implement the dynamic programming approach to find the length of the longest increasing subsequence in `nums`. */
{
    let n = nums.len();
    if n == 0 {
        return 0i32;
    }

    let mut dp: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            dp.len() == i,
            forall|idx: int| 0 <= idx < i ==> dp[idx] >= 1,
            forall|j: int, k: int| 0 <= j < k && k < i ==> (nums[j].view() < nums[k].view() ==> dp[j] <= dp[k]),
        decreases (n - i) as nat
    {
        dp.push(1);
        let mut j = 0;
        while j < i
            invariant
                0 <= j && j <= i,
                dp.len() == i + 1,
                forall|idx: int| 0 <= idx < i + 1 ==> dp[idx] >= 1,
                forall|k: int, l: int| 0 <= k < l && l < i + 1 ==> (nums[k].view() < nums[l].view() ==> dp[k] <= dp[l]),
            decreases (i - j) as nat
        {
            if nums[i].view() > nums[j].view() {
                dp.set(i, max(dp[i], dp[j] + 1));
            }
            j = j + 1;
        }
        i = i + 1;
    }

    let mut max_len = 0;
    if n > 0 {
        max_len = dp[0];
        let mut i = 1;
        while i < n
            invariant
                0 <= i && i <= n,
                dp.len() == n,
                max_len >= 1,
                forall|j: int| 0 <= j < i ==> max_len >= dp[j],
                forall|j: int| 0 <= j < n ==> dp[j] >= 1,
            decreases (n - i) as nat
        {
            max_len = max(max_len, dp[i]);
            i = i + 1;
        }
    }
    max_len
}
// </vc-code>

}
fn main() {}