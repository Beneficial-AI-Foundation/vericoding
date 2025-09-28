// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix index access syntax and improve verification */
proof fn increasing_subsegment_bound(n: int) -> (bound: int)
    ensures
        bound >= 0,
        bound <= n
{
    if n <= 0 {
        0
    } else {
        n
    }
}

proof fn is_increasing_subsegment(nums: &Vec<i32>, start: int, end: int) -> (res: bool)
    requires
        start >= 0,
        end <= nums.len() as int,
        start <= end
    ensures
        res ==> (
            forall|i: int, j: int| start <= i < j < end ==> #[trigger] nums[i] <= #[trigger] nums[j]
        )
{
    if start >= end {
        true
    } else {
        let all_increasing = forall|i: int, j: int| start <= i < j < end ==> nums[i] <= nums[j];
        all_increasing
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
/* code modified by LLM (iteration 5): Fix index access syntax and implement LIS algorithm */
{
    let n = nums.len();
    let mut result = 0;
    
    if n > 0 {
        let mut dp = Vec::new();
        dp.push(1);
        result = 1;
        
        for i in 1..n {
            let mut max_val = 0;
            for j in 0..i {
                if nums[j] < nums[i] {
                    if dp[j] > max_val {
                        max_val = dp[j];
                    }
                }
            }
            dp.push(max_val + 1);
            if dp[i] > result {
                result = dp[i];
            }
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}