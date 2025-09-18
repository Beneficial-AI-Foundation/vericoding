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
/* helper modified by LLM (iteration 5): chain length from parent pointers */
spec fn chain_len(parent: Seq<int>, i: int) -> int
    requires
        0 <= i < parent.len(),
        forall|k: int| 0 <= k < parent.len() ==> parent[k] >= -1 && parent[k] < k,
    decreases
        i,
    ensures
        result >= 1,
{
    if parent[i] == -1 {
        1
    } else {
        proof {
            assert(parent[i] >= 0);
            assert(parent[i] < parent.len());
        }
        1 + chain_len(parent, parent[i])
    }
}

/* helper modified by LLM (iteration 5): reconstruct increasing subsequence ending at i */
spec fn reconstruct_seq(xs: Seq<i32>, parent: Seq<int>, i: int) -> Seq<i32>
    requires
        0 <= i < xs.len(),
        parent.len() == xs.len(),
        forall|k: int| 0 <= k < parent.len() ==> parent[k] >= -1 && parent[k] < k,
    decreases
        i,
    ensures
        is_subsequence_of(result, xs) && is_strictly_increasing(result) && result.len() == chain_len(parent, i) && result@[result.len() - 1] == xs@[i],
{
    if parent[i] == -1 {
        seq![xs@[i]]
    } else {
        proof {
            assert(parent[i] >= 0);
            assert(parent[i] < parent.len());
        }
        let prev = reconstruct_seq(xs, parent, parent[i]);
        prev + seq![xs@[i]]
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
    /* code modified by LLM (iteration 5): dynamic programming to compute LIS length and track parent pointers */
    let n_usize = xs.len();
    let n = n_usize as int;
    if n_usize == 0 {
        proof {
            let subseq = seq![];
            assert(is_subsequence_of(subseq, xs@));
            assert(is_strictly_increasing(subseq));
            assert(subseq.len() == 0);
        }
        return 0;
    }
    let mut parent: Vec<int> = Vec::from_elem(n_usize, -1);
    let mut len_vec: Vec<usize> = Vec::from_elem(n_usize, 1usize);
    let mut i: int = 0;
    let mut max_len: usize = 1usize;
    let mut max_idx: usize = 0usize;
    while i < n
        invariant
            0 <= i && i <= n,
            forall|t: int| 0 <= t < i ==> len_vec[t as usize] as int == chain_len(parent@, t) && len_vec[t as usize] >= 1 && parent[t as usize] >= -1 && parent[t as usize] < t,
        decreases
            n - i
    {
        let mut j: int = 0;
        while j < i
            invariant
                0 <= j && j <= i,
                forall|t: int| 0 <= t < j ==> len_vec[t as usize] as int == chain_len(parent@, t) && len_vec[t as usize] >= 1 && parent[t as usize] >= -1 && parent[t as usize] < t,
            decreases
                i - j
        {
            if xs@[j] < xs@[i] {
                let cand = len_vec[j as usize] + 1;
                if cand > len_vec[i as usize] {
                    len_vec[i as usize] = cand;
                    parent[i as usize] = j;
                }
            }
            j = j + 1;
        }
        if len_vec[i as usize] > max_len {
            max_len = len_vec[i as usize];
            max_idx = i as usize;
        }
        i = i + 1;
    }
    proof {
        assert(0 <= max_idx as int && max_idx as int < n);
        assert(len_vec[max_idx] as int == chain_len(parent@, max_idx as int));
        assert(max_len as int == len_vec[max_idx] as int);
    }
    let subseq = reconstruct_seq(xs@, parent@, max_idx as int);
    proof {
        assert(subseq.len() == chain_len(parent@, max_idx as int));
        assert(is_subsequence_of(subseq, xs@));
        assert(is_strictly_increasing(subseq));
        assert(len_vec[max_idx] as int == chain_len(parent@, max_idx as int));
        assert(max_len as int == len_vec[max_idx] as int);
        assert(subseq.len() == max_len as int);
    }
    max_len
}

// </vc-code>

}
fn main() {}