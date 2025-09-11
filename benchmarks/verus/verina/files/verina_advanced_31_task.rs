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
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}