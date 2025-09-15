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
/* helper modified by LLM (iteration 5): max_usize */
fn max_usize(a: usize, b: usize) -> usize { if a > b { a } else { b } }

/* helper modified by LLM (iteration 5): vec_to_seq */
spec fn vec_to_seq(v: &Vec<i32>) -> Seq<i32> { v@ }
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
    /* code modified by LLM (iteration 5): use Seq.index(...) method instead of @[...] indexing to work with vstd::seq::Seq */
    let n = xs.len();

    // compute LIS length ending at each position
    let mut lens: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let mut best: usize = 1;
        let mut j: usize = 0;
        while j < i {
            if xs[j] < xs[i] {
                let cand = lens[j] + 1;
                if cand > best { best = cand; }
            }
            j += 1;
        }
        lens.push(best);
        i += 1;
    }

    // overall result is the maximum of lens
    let mut result: usize = 0;
    let mut k: usize = 0;
    while k < n {
        if lens[k] > result { result = lens[k]; }
        k += 1;
    }

    proof {
        let seq = xs@;
        let lens_seq: Seq<usize> = lens@;
        if n == 0 {
            let subseq: Seq<i32> = Seq::empty();
            assert(subseq.len() == 0);
            assert(is_subsequence_of(subseq, seq));
            assert(is_strictly_increasing(subseq));
        } else {
            // find an index p with lens[p] == result
            let mut p: usize = 0;
            while p < n && lens_seq.index(p as int) != result { p += 1; }
            assert(p < n);

            // build indices of a subsequence ending at p by following DP predecessors
            let mut idxs: Seq<int> = Seq::empty();
            let mut cur: usize = p;
            loop {
                idxs = Seq::push(idxs, cur as int);
                if lens_seq.index(cur as int) <= 1usize { break; }
                // find j < cur with lens[j] + 1 == lens[cur] and seq[j] < seq[cur]
                let mut j: usize = 0;
                while !(j < cur && seq.index(j as int) < seq.index(cur as int) && lens_seq.index(j as int) + 1usize == lens_seq.index(cur as int)) { j += 1; }
                assert(j < cur);
                cur = j;
            }

            // reverse idxs to obtain increasing indices order and build the subsequence of values
            let mut subseq: Seq<i32> = Seq::empty();
            let mut r: int = idxs.len() - 1;
            while r >= 0 {
                let idx: int = idxs.index(r);
                subseq = Seq::push(subseq, seq.index(idx));
                if r == 0 { break; }
                r = r - 1;
            }

            // verify properties
            assert(subseq.len() == result);
            assert(is_subsequence_of(subseq, seq));
            assert(is_strictly_increasing(subseq));
        }

        // maximality: any strictly increasing subsequence cannot be longer than `result`.
        assert(forall|subseq: Seq<i32>| (is_subsequence_of(subseq, seq) && is_strictly_increasing(subseq)) ==> subseq.len() <= result);
    }

    result
}
// </vc-code>

}
fn main() {}