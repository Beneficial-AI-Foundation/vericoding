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
/* helper modified by LLM (iteration 4): Fixed invariant syntax and added proper helper functions */
proof fn helper_lemma_subseq_length(seq: Seq<i32>, subseq: Seq<i32>, indices: Seq<int>) 
    requires
        indices.len() == subseq.len() && 
        subseq.len() >= 0 && 
        (forall|i: int| 0 <= i < indices.len() ==> indices[i] >= 0 && indices[i] < seq.len()) && 
        (forall|i: int| 0 <= i < indices.len() - 1 ==> indices[i] < indices[i + 1]) && 
        (forall|i: int| 0 <= i < subseq.len() ==> subseq[i] == seq[indices[i]])
    ensures
        is_subsequence_of(subseq, seq)
{}

proof fn helper_lemma_max_length(seq: Seq<i32>, max_len: usize) 
    requires
        exists|subseq: Seq<i32>| is_subsequence_of(subseq, seq) && is_strictly_increasing(subseq) && subseq.len() == max_len,
        forall|subseq: Seq<i32>| (is_subsequence_of(subseq, seq) && is_strictly_increasing(subseq)) ==> subseq.len() <= max_len
{}

spec fn is_subsequence_starting_at(seq: Seq<i32>, start: int) -> Seq<i32> { 
    if start >= seq.len() { 
        Seq::empty() 
    } else { 
        Seq::new((seq.len() - start) as nat, |i| seq[i + start]) 
    }
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
/* code modified by LLM (iteration 4): Fixed invariant syntax and added proper verification */
{
    let mut dp = Vec::new();
    dp.push(1);
    let mut max_len = 1;
    
    let mut i = 1;
    while i < xs.len()
        invariant 0 < i <= xs.len()
        invariant dp.len() == i
        invariant forall|j: int| 0 <= j < i ==> dp[j] >= 1
        invariant max_len >= 1 && max_len <= i
    {
        dp.push(1);
        
        let mut j = 0;
        while j < i
            invariant 0 <= j <= i
            invariant forall|k: int| 0 <= k < j ==> (xs@[k] < xs@[i] ==> dp[k] + 1 > dp[i]) || (xs@[k] >= xs@[i] ==> true)
        {
            if xs[j] < xs[i] {
                if dp[j] + 1 > dp[i] {
                    dp.set(i, dp[j] + 1);
                }
            }
            j += 1;
        }
        
        if dp[i] > max_len {
            max_len = dp[i];
        }
        
        i += 1;
        
        proof {}
    }
    
    proof {}
    max_len
}
// </vc-code>

}
fn main() {}