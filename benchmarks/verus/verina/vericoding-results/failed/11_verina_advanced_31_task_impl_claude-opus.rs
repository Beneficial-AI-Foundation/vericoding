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
spec fn max(a: int, b: int) -> int {
    if a > b { a } else { b }
}

spec fn lis_ending_at(seq: Seq<i32>, end: int) -> int
    decreases end
{
    if end <= 0 {
        1
    } else {
        let mut max_len = 1;
        let mut i = 0;
        while i < end
            invariant
                0 <= i <= end,
                forall|j: int| 0 <= j < i && seq[j] < seq[end] ==> max_len >= lis_ending_at(seq, j) + 1,
                max_len >= 1
        {
            if seq[i] < seq[end] {
                max_len = max(max_len, lis_ending_at(seq, i) + 1);
            }
            i = i + 1;
        }
        max_len
    }
}

proof fn lis_ending_at_is_valid(seq: Seq<i32>, end: int)
    requires
        0 <= end < seq.len()
    ensures
        exists|subseq: Seq<i32>|
            is_subsequence_of(subseq, seq.take(end + 1)) &&
            is_strictly_increasing(subseq) &&
            subseq.len() == lis_ending_at(seq, end) &&
            subseq.last() == seq[end],
        forall|subseq: Seq<i32>|
            (is_subsequence_of(subseq, seq.take(end + 1)) &&
             is_strictly_increasing(subseq) &&
             subseq.last() == seq[end])
            ==> subseq.len() <= lis_ending_at(seq, end)
    decreases end
{
    if end == 0 {
        let subseq = seq![seq[0]];
        let indices = seq![0int];
        assert(is_subsequence_of(subseq, seq.take(1))) by {
            assert(indices.len() == subseq.len());
            assert(forall|i: int| 0 <= i < indices.len() ==> indices[i] >= 0 && indices[i] < seq.take(1).len());
            assert(forall|i: int| 0 <= i < indices.len() - 1 ==> indices[i] < indices[i + 1]);
            assert(forall|i: int| 0 <= i < subseq.len() ==> subseq[i] == seq.take(1)[indices[i]]);
        }
        assert(is_strictly_increasing(subseq));
        assert(subseq.last() == seq[0]);
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
{
    if xs.len() == 0 {
        return 0;
    }
    
    let mut dp = Vec::new();
    let mut i = 0;
    while i < xs.len()
        invariant
            dp.len() == i,
            forall|j: int| 0 <= j < i ==> dp[j] >= 1,
            forall|j: int| 0 <= j < i ==> exists|subseq: Seq<i32>|
                is_subsequence_of(subseq, xs@.take(j + 1)) &&
                is_strictly_increasing(subseq) &&
                subseq.len() == dp[j] &&
                subseq.last() == xs@[j],
            forall|j: int| 0 <= j < i ==> forall|subseq: Seq<i32>|
                (is_subsequence_of(subseq, xs@.take(j + 1)) &&
                 is_strictly_increasing(subseq) &&
                 subseq.last() == xs@[j])
                ==> subseq.len() <= dp[j]
    {
        let mut max_len: usize = 1;
        let mut j = 0;
        while j < i
            invariant
                0 <= j <= i,
                i < xs.len(),
                dp.len() == i,
                max_len >= 1,
                forall|k: int| 0 <= k < j && xs[k] < xs[i] ==> max_len >= dp[k] + 1
        {
            if xs[j] < xs[i] && dp[j] + 1 > max_len {
                max_len = dp[j] + 1;
            }
            j = j + 1;
        }
        dp.push(max_len);
        i = i + 1;
    }
    
    let mut result: usize = 0;
    let mut i = 0;
    while i < dp.len()
        invariant
            0 <= i <= dp.len(),
            dp.len() == xs.len(),
            forall|j: int| 0 <= j < i ==> result >= dp[j]
    {
        if dp[i] > result {
            result = dp[i];
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}