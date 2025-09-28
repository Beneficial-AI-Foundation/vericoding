// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec helper to convert usize to int */
spec fn usize_to_int(x: usize) -> int {
    x as int
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
    /* code modified by LLM (iteration 5): standard DP with invariants using int-indexed forall and casts */
    if nums.len() == 0 {
        0
    } else {
        let n = nums.len();
        let mut dp: Vec<i32> = Vec::new();
        let mut i = 0usize;
        while i < n
            invariant
                i <= n,
                dp.len() == i,
            decreases n - i
        {
            dp.push(1);
            i += 1;
        }
        let mut j = 0usize;
        let mut res: i32 = 1;
        while j < n
            invariant
                j <= n,
                dp.len() == n,
                forall |idx: int| 0 <= idx && idx < j as int ==> dp[idx as usize] <= (idx + 1) as i32,
                res >= 1,
                res <= n as i32,
            decreases n - j
        {
            proof {
                assert(j < n);
            }
            let mut k = 0usize;
            while k < j
                invariant
                    k <= j,
                    k < n,
                    dp.len() == n,
                    forall |idx: int| 0 <= idx && idx < j as int ==> dp[idx as usize] <= (idx + 1) as i32,
                decreases j - k
            {
                proof {
                    assert(k < n);
                    assert(j < n);
                    assert(dp.len() == n);
                    assert(k < j);
                    assert(dp[k] <= (k as int + 1) as i32);
                }
                if nums[k] < nums[j] {
                    let candidate = dp[k] + 1;
                    if candidate > dp[j] {
                        dp[j] = candidate;
                    }
                }
                k += 1;
            }
            if dp[j] > (j as int + 1) as i32 {
                dp[j] = (j as int + 1) as i32;
            }
            if dp[j] > res {
                res = dp[j];
            }
            j += 1;
        }
        res
    }
}

// </vc-code>

}
fn main() {}