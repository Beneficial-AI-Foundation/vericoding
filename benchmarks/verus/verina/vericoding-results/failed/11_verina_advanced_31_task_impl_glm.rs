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
proof fn helper_is_strictly_increasing(seq: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < seq.len() - 1 ==> #[trigger] seq[i] < seq[i + 1]
}

proof fn helper_is_subsequence_of(subseq: Seq<i32>, seq: Seq<i32>) -> bool {
    exists|indices: Seq<int>| 
        indices.len() == subseq.len() &&
        #[trigger] indices.len() >= 0 &&
        (forall|i: int| 0 <= i < indices.len() ==> #[trigger] indices[i] >= 0 && indices[i] < seq.len()) &&
        (forall|i: int| 0 <= i < indices.len() - 1 ==> #[trigger] indices[i] < indices[i + 1]) &&
        (forall|i: int| 0 <= i < subseq.len() ==> #[trigger] subseq[i] == seq[indices[i]])
}

/* helper modified by LLM (iteration 2): added max function for usize */
fn max(a: usize, b: usize) -> usize {
    if a < b { b } else { a }
}
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
/* code modified by LLM (iteration 2): fixed max function usage and outer invariant */
{
    let n = xs.len();
    if n == 0 {
        return 0;
    }
    
    let mut dp = vec![1; n];
    let mut max_len = 1;
    
    let mut i = 1;
    while i < n
        invariant
            1 <= i <= n,
            forall|j: int| 0 <= j < i ==> dp[j] >= 1,
            max_len >= 1,
            forall|k: int| 0 <= k < i ==> dp[k] <= max_len,
            exists|k: int| 0 <= k < i && dp[k] == max_len,
        decreases n - i
    {
        let mut j = 0;
        while j < i
            invariant
                0 <= j <= i,
                dp[i] == 1,
            decreases i - j
        {
            if xs[j] < xs[i] {
                dp[i] = max(dp[i], dp[j] + 1);
            }
            j += 1;
        }
        
        if dp[i] > max_len {
            max_len = dp[i];
        }
        i += 1;
    }
    
    max_len
}
// </vc-code>

}
fn main() {}