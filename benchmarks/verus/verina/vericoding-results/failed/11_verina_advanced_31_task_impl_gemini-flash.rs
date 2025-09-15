// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subsequence_of(subseq: Seq<i32>, seq: Seq<i32>) -> bool {
    exists|indices: Seq<int>| 
        indices.len() == subseq.len() &&
        #[trigger] indices.len() >= 0 &&
        (forall|i: int| 0 <= i < indices.len() ==> #[trigger] indices[i] >= 0 && indices[i] < seq.len()) &&
        (forall|i: int| 0 <= i < indices.len() - 1 ==> #[trigger] indices[i] < indices[i + 1]) &&
        (forall|i: int| 0 <= i < subseq.len() ==> #[trigger] subseq[i] == seq[indices[i]])
}

spec fn is_strictly_increasing(seq: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < seq.len() - 1 ==> #[trigger] seq[i] < seq[i + 1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Retained the max helper function as it is correct. */
spec fn max(a: int, b: int) -> int { if a >= b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subseq_length(xs: &Vec<i32>) -> (result: usize)
    ensures

        exists|subseq: Seq<i32>| 
            is_subsequence_of(subseq, xs@) && 
            is_strictly_increasing(subseq) && 
            subseq.len() == result,

        forall|subseq: Seq<i32>| 
            (is_subsequence_of(subseq, xs@) && is_strictly_increasing(subseq)) 
            ==> subseq.len() <= result,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed loop variable types from `int` to `usize`, as `int` is for ghost code only. Updated loop conditions to `i < n` and `j < i` directly without casting. */
{
    let n = xs.len();
    if n == 0 {
        return 0;
    }

    let mut dp: Vec<int> = Vec::new();
    dp.reserve(n);

    for _ in 0..n {
        dp.push(1);
    }

    let mut i: usize = 1;
    while i < n
        invariant
            dp.len() == n,
            0 <= i as int && i as int <= n as int,
            forall|idx: int| 0 <= idx && idx < i as int ==> dp[idx] > 0,
    {
        let mut j: usize = 0;
        while j < i
            invariant
                dp.len() == n,
                0 <= j as int && j as int <= i as int,
                0 <= i as int && i as int <= n as int,
                forall|idx: int| 0 <= idx && idx < j as int ==> dp[idx] > 0,
        {
            if xs@[i] > xs@[j] {
                let dp_i = dp[i];
                let dp_j = dp[j];
                dp.set(i, max(dp_i, dp_j + 1));
            }
            j = j + 1;
        }
        i = i + 1;
    }

    let mut max_len: int = 0;
    if n > 0 {
        max_len = dp[0];
    }
    let mut k: usize = 1;
    while k < n
        invariant
            dp.len() == n,
            0 <= k as int && k as int <= n as int,
            max_len == max_len_dp_prefix(dp.view(), k as int),
    {
        max_len = max(max_len, dp[k]);
        k = k + 1;
    }
    
    max_len as usize
}
// </vc-code>

}
fn main() {}