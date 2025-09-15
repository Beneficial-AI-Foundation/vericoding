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
/* code modified by LLM (iteration 5): Fixed compilation error by removing space after exists and forall in assert statements */
{
    if xs.len() == 0 {
        return 0;
    }
    let seq = xs@;
    let len = seq.len() as int;
    let mut dp: Vec<usize> = Vec::with_capacity(len as usize);
    for _ in 0..len {
        dp.push(1);
    }
    for i in 0..len {
        for j in 0..i {
            if seq[j] < seq[i] {
                let dp_j = dp@[j];
                if dp_j + 1 > dp@[i] {
                    dp.set(i as usize, dp_j + 1);
                }
            }
        }
    }
    let mut max_len = 0;
    for k in 0..len {
        let current = dp@[k];
        if current > max_len {
            max_len = current;
        }
    }
    proof {
        assert exists|subseq: Seq<i32>| #[auto] is_subsequence_of(subseq, seq) && is_strictly_increasing(subseq) && subseq.len() == max_len as int;
        assert forall|subseq: Seq<i32>| #[auto] (is_subsequence_of(subseq, seq) && is_strictly_increasing(subseq)) ==> subseq.len() <= max_len as int;
    }
    max_len
}
// </vc-code>

}
fn main() {}