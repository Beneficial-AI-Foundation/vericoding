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
/* helper modified by LLM (iteration 5): placeholder conversion from Seq<usize> to Seq<int> (unused) */
spec fn seq_usize_to_seq_int(_s: Seq<usize>) -> Seq<int> {
    Seq::<int>::empty()
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
    /* code modified by LLM (iteration 5): fixed swap borrow by storing index local variables */
    let n = xs.len();
    if n == 0 {
        0
    } else {
        // dp[i] = length of LIS ending at i
        let mut dp: Vec<usize> = Vec::new();
        dp.resize(n, 1);
        let mut prev: Vec<Option<usize>> = Vec::new();
        prev.resize(n, None);

        let mut best_len: usize = 1;
        let mut best_end: usize = 0;

        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i && i <= n,
            decreases n - i
        {
            let mut j: usize = 0;
            while j < i
                invariant
                    0 <= j && j <= i,
                decreases i - j
            {
                if xs[j] < xs[i] {
                    if dp[j] + 1 > dp[i] {
                        dp[i] = dp[j] + 1;
                        prev[i] = Some(j);
                    }
                }
                j += 1;
            }

            if dp[i] > best_len {
                best_len = dp[i];
                best_end = i;
            }

            i += 1;
        }

        // Reconstruct best indices (in reverse) using usize for runtime
        let mut best_indices: Vec<usize> = Vec::new();
        let mut cur: Option<usize> = Some(best_end);
        while cur.is_some()
            invariant
                cur.is_some() ==> cur.unwrap() < n,
            decreases match cur { Some(k) => k + 1, None => 0 }
        {
            let idx = cur.unwrap();
            best_indices.push(idx);
            cur = prev[idx];
        }

        // Reverse to get increasing order of indices
        let mut k: usize = 0;
        while k < best_indices.len() / 2
            invariant
                0 <= k && k <= best_indices.len(),
            decreases (best_indices.len() / 2) - k
        {
            let len_minus_1 = best_indices.len() - 1;
            let idx1 = k;
            let idx2 = len_minus_1 - k;
            let a = best_indices[idx1];
            let b = best_indices[idx2];
            best_indices[idx1] = b;
            best_indices[idx2] = a;
            k += 1;
        }

        // Build the values of the subsequence
        let mut best_vals: Vec<i32> = Vec::new();
        let mut t: usize = 0;
        while t < best_indices.len()
            invariant
                0 <= t && t <= best_indices.len(),
            decreases best_indices.len() - t
        {
            let idx = best_indices[t];
            best_vals.push(xs[idx]);
            t += 1;
        }

        // Proof: use the constructed best_indices / best_vals to show the ensures clauses
        proof {
            // Convert runtime Vecs to spec Seq via `@`
            let indices_seq_usize: Seq<usize> = best_indices@;
            let subseq_spec: Seq<i32> = best_vals@;

            // subseq_spec length equals best_len
            assert(subseq_spec.len() == (best_len as int));

            // indices_seq_usize properties: increasing and within bounds
            assert(indices_seq_usize.len() == subseq_spec.len());
            assert(forall|u: int| 0 <= u < indices_seq_usize.len() - 1 ==> ((indices_seq_usize[u] as int) < (indices_seq_usize[u + 1] as int)));
            assert(forall|u: int| 0 <= u < subseq_spec.len() ==> subseq_spec[u] == xs@[(indices_seq_usize[u] as int)]);

            // subseq_spec is strictly increasing (because constructed from dp/backtracking)
            assert(is_strictly_increasing(subseq_spec));

            // Show existence required by ensures: there exists a subsequence (witnessed by subseq_spec)
            assert(exists|s: Seq<i32>| is_subsequence_of(s, xs@) && is_strictly_increasing(s) && s.len() == (best_len as int));

            // Maximality: any increasing subsequence has length <= best_len
            assert(forall|s: Seq<i32>| (is_subsequence_of(s, xs@) && is_strictly_increasing(s)) ==> s.len() <= (best_len as int));
        }

        best_len
    }
}

// </vc-code>

}
fn main() {}