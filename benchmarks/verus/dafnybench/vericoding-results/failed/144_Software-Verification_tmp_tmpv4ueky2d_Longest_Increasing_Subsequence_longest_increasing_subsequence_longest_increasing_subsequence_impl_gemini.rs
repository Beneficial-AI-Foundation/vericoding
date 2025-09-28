// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn find_max(x: int, y: int) -> int {
    if x > y { x } else { y }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fix decreases clause type annotation */
spec fn lis_ending_at(s: Seq<i32>, i: int) -> int
    recommends 0 <= i < s.len()
    decreases i, 1int
{
    1 + max_lis_len_filtered(s, i)
}

/* helper modified by LLM (iteration 3): fix decreases clause type annotation */
spec fn max_lis_len_filtered(s: Seq<i32>, i: int) -> int
    recommends 0 <= i < s.len()
    decreases i, 0int
{
    if i == 0 {
        0
    } else {
        let j = i - 1;
        let rest_max = max_lis_len_filtered(s, j);
        if s[j] < s[i] {
            find_max(rest_max, lis_ending_at(s, j))
        } else {
            rest_max
        }
    }
}

spec fn max_lis_len_filtered_upto(s: Seq<i32>, i: int, k: int) -> int
    recommends
        0 <= i < s.len(),
        0 <= k <= i,
    decreases k
{
    if k == 0 {
        0
    } else {
        let j = k - 1;
        let rest_max = max_lis_len_filtered_upto(s, i, j);
        if s[j] < s[i] {
            find_max(rest_max, lis_ending_at(s, j))
        } else {
            rest_max
        }
    }
}

proof fn lemma_upto_eq_filtered(s: Seq<i32>, i: int)
    requires 0 <= i < s.len()
    ensures max_lis_len_filtered(s, i) == max_lis_len_filtered_upto(s, i, i)
    decreases i
{
    if i > 0 {
        lemma_upto_eq_filtered(s, i - 1);
    }
}

/* helper modified by LLM (iteration 3): fix decreases clause type annotation */
proof fn lemma_max_lis_ge_0(s: Seq<i32>, i: int)
    requires 0 <= i < s.len()
    ensures max_lis_len_filtered(s, i) >= 0
    decreases i, 0int
{
    if i > 0 {
        let j = i - 1;
        lemma_max_lis_ge_0(s, j);
        if s[j] < s[i] {
            lemma_lis_at_least_1(s, j);
        }
    }
}

/* helper modified by LLM (iteration 3): fix decreases clause type annotation */
proof fn lemma_lis_at_least_1(s: Seq<i32>, i: int)
    requires 0 <= i < s.len()
    ensures lis_ending_at(s, i) >= 1
    decreases i, 1int
{
    lemma_max_lis_ge_0(s, i);
}
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: &Vec<i32>) -> (max: i32)
    requires 
        1 <= nums.len() <= 2500,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] >= -10000 && #[trigger] nums[i] <= 10000,

    ensures 
        max >= 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): replaced `vec_with_len` with `vec!` macro to fix compilation error */
    let n = nums.len();
    let s = nums.view();

    let mut dp = vec![1; n];

    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i <= n,
            nums.view() == s,
            dp.len() == n,
            forall|k: int| 0 <= k < i ==> dp[k] == lis_ending_at(s, k),
            forall|k: int| i <= k < n ==> dp[k] == 1,
        decreases n - i
    {
        let mut max_prev_len = 0;
        let mut j: usize = 0;
        while j < i
            invariant
                0 <= j <= i,
                1 <= i < n,
                nums.view() == s,
                dp.len() == n,
                forall|k: int| 0 <= k < i ==> dp[k] == lis_ending_at(s, k),
                max_prev_len == max_lis_len_filtered_upto(s, i as int, j as int),
            decreases i - j
        {
            if nums[j] < nums[i] {
                if dp[j] > max_prev_len {
                    max_prev_len = dp[j];
                }
            }
            j = j + 1;
        }

        proof {
            lemma_upto_eq_filtered(s, i as int);
        }
        let dp_i = 1 + max_prev_len;
        dp.set(i, dp_i);

        i = i + 1;
    }

    let mut max_len = dp[0];
    let mut k: usize = 1;
    while k < n
        invariant
            1 <= k <= n,
            nums.view() == s,
            dp.len() == n,
            forall|l: int| 0 <= l < n ==> dp[l] == lis_ending_at(s, l),
            exists|j: int| 0 <= j < k && max_len == dp[j],
            forall|j: int| 0 <= j < k ==> dp[j] <= max_len,
        decreases n - k
    {
        if dp[k] > max_len {
            max_len = dp[k];
        }
        k = k + 1;
    }

    proof {
        let chosen_idx = choose|j: int| 0 <= j < n && max_len == dp[j];
        lemma_lis_at_least_1(s, chosen_idx);
    }

    max_len
}
// </vc-code>

}
fn main() {}