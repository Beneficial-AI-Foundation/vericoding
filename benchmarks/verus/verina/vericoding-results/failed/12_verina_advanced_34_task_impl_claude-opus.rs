// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_increasing_subsequence(nums: Seq<i32>, subseq: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < subseq.len() ==> #[trigger] subseq[i] < #[trigger] subseq[j]
}

spec fn subsequence_of(nums: Seq<i32>, indices: Seq<int>) -> Seq<i32>
    recommends
        forall|i: int| 0 <= i < indices.len() ==> 0 <= #[trigger] indices[i] < nums.len(),
        forall|i: int, j: int| 0 <= i < j < indices.len() ==> #[trigger] indices[i] < #[trigger] indices[j],
{
    Seq::new(indices.len(), |i: int| nums[indices[i]])
}

spec fn max(a: int, b: int) -> int {
    if a > b { a } else { b }
}
/* helper modified by LLM (iteration 5): Added trigger annotations to quantifiers in subsequence_of */
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        result <= nums.len() as i32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes to code, only fixing helper trigger annotations */
    let n = nums.len();
    if n == 0 {
        return 0;
    }
    
    let mut dp: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            dp.len() == i,
            forall|k: int| 0 <= k < i ==> 1 <= dp[k] <= k + 1,
            forall|k: int| 0 <= k < i ==> dp[k] <= n as int,
        decreases n - i
    {
        let mut max_len: i32 = 1;
        let mut j: usize = 0;
        while j < i
            invariant
                j <= i,
                1 <= max_len <= i as i32 + 1,
                max_len <= n as i32,
            decreases i - j
        {
            if nums[j] < nums[i] {
                if dp[j] + 1 > max_len {
                    max_len = dp[j] + 1;
                }
            }
            j = j + 1;
        }
        dp.push(max_len);
        i = i + 1;
    }
    
    let mut result: i32 = 0;
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            0 <= result <= n as i32,
            dp.len() == n,
        decreases n - k
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