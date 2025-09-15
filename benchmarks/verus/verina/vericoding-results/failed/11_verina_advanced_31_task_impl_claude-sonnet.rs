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
/* helper modified by LLM (iteration 5): fixed spec functions to not use mutable variables and loops - spec functions must be pure */
spec fn max_increasing_length_at(xs: Seq<i32>, end_idx: int) -> nat
    decreases end_idx
{
    if end_idx < 0 { 0 }
    else {
        1 + (max_over_range(xs, end_idx, 0))
    }
}

spec fn max_over_range(xs: Seq<i32>, end_idx: int, start_idx: int) -> nat
    decreases end_idx - start_idx
{
    if start_idx >= end_idx { 0 }
    else {
        let current = if xs[start_idx] < xs[end_idx] { max_increasing_length_at(xs, start_idx) } else { 0 };
        let rest = max_over_range(xs, end_idx, start_idx + 1);
        if current > rest { current } else { rest }
    }
}

spec fn max_increasing_length(xs: Seq<i32>) -> nat {
    if xs.len() == 0 { 0 }
    else {
        max_length_over_positions(xs, 0)
    }
}

spec fn max_length_over_positions(xs: Seq<i32>, pos: int) -> nat
    decreases xs.len() - pos
{
    if pos >= xs.len() { 0 }
    else {
        let current = max_increasing_length_at(xs, pos);
        let rest = max_length_over_positions(xs, pos + 1);
        if current > rest { current } else { rest }
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
/* code modified by LLM (iteration 5): added decreases clauses to all loops */
{
    if xs.len() == 0 {
        return 0;
    }
    
    let mut dp: Vec<usize> = Vec::with_capacity(xs.len());
    let mut i: usize = 0;
    while i < xs.len()
        invariant i <= xs.len(), dp.len() == i
        decreases xs.len() - i
    {
        dp.push(1);
        i = i + 1;
    }
    
    i = 1;
    while i < xs.len()
        decreases xs.len() - i
    {
        let mut j: usize = 0;
        while j < i
            decreases i - j
        {
            if xs[j] < xs[i] && dp[j] + 1 > dp[i] {
                let new_val = dp[j] + 1;
                dp.set(i, new_val);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    let mut max_len = 0;
    i = 0;
    while i < dp.len()
        decreases dp.len() - i
    {
        if dp[i] > max_len {
            max_len = dp[i];
        }
        i = i + 1;
    }
    
    max_len
}
// </vc-code>

}
fn main() {}