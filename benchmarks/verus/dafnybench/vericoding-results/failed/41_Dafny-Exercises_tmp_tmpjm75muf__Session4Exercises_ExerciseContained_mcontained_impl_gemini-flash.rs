use vstd::prelude::*;

verus! {

spec fn strict_sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] < s[w]
}

// <vc-helpers>
spec fn seq_strict_sorted_subseq(s: Seq<i32>, start: int, end_exclusive: int) -> bool
{
    forall|u: int, w: int| start <= u < w < end_exclusive ==> s[u] < s[w]
}

proof fn lemma_subseq_strict_sorted(s: Seq<i32>, start: int, end_exclusive: int)
    requires
        strict_sorted(s),
        0 <= start <= end_exclusive <= s.len(),
    ensures
        seq_strict_sorted_subseq(s, start, end_exclusive),
{
    assert forall|u: int, w: int| start <= u < w < end_exclusive implies s[u] < s[w] by {
        assert(strict_sorted(s)); // This is the assumption
        assert(0 <= u < w < s.len()); // This follows from 0 <= start <= u < w < end_exclusive <= s.len()
    }
}
// </vc-helpers>

// <vc-spec>
fn mcontained(v: &[i32], w: &[i32], n: usize, m: usize) -> (b: bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
    requires 
        n <= m,
        n >= 0,
        strict_sorted(v@),
        strict_sorted(w@),
        v@.len() >= n,
        w@.len() >= m,
    ensures
        b == forall|k: int| 0 <= k < n ==> w@.subrange(0, m as int).contains(v@[k])
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0; // Pointer for v
    let mut j: int = 0; // Pointer for w

    let v_seq = v@;
    let w_seq = w@;

    proof {
        lemma_subseq_strict_sorted(v_seq, 0, n as int);
        lemma_subseq_strict_sorted(w_seq, 0, m as int);
    }

    // `i` tracks the index in `v` that we are currently trying to find in `w`.
    // `j` tracks the index in `w` where we are looking for `v[i]`.
    while i < n
    invariant_po {
        0 <= i <= n,
        0 <= j <= m,
        // All elements v[0..i-1] have been found in w[0..m-1]
        forall|k: int| 0 <= k < i ==> w_seq.subrange(0, m as int).contains(v_seq[k]),
        // The search for v[i] starts from index j in w.
        // This means for any l < j, w[l] < v[i] (if i < n).
        // Or, more precisely, if v[i] exists, it must be at or after w[j].
        // If i < n and j < m, then v_seq[i] > w_seq[j-1] (if j>0)
        i < n ==> (j == 0 || (j > 0 && w_seq[j-1] < v_seq[i])),
    }
    {
        while j < m && w_seq[j] < v_seq[i]
        invariant_po {
            0 <= i < n,
            0 <= j <= m,
            // All elements v[0..i-1] have been found in w[0..m-1]
            forall|k: int| 0 <= k < i ==> w_seq.subrange(0, m as int).contains(v_seq[k]),
            // All w_seq elements from 0 to j-1 are smaller than v_seq[i]
            forall|l: int| 0 <= l < j ==> w_seq[l] < v_seq[i],
        }
        {
            j = j + 1;
        }

        // If we reached the end of `w` or `w[j]` is greater than `v[i]`,
        // it means `v[i]` is not found in `w` at or after `w[j]`.
        // Because both `v` and `w` are strictly sorted, if `v[i]` exists in `w`,
        // it must be `w[j]` (if `w[j] == v[i]`) or it doesn't exist.
        if j == m || w_seq[j] > v_seq[i] {
            // v[i] is not found in w
            proof {
                assert forall |k: int| 0 <= k < m implies w_seq[k] != v_seq[i] by {
                    if (0 <= k && k < j) {
                        assert(w_seq[k] < v_seq[i]);
                    } else if (j <= k && k < m) {
                        assert(seq_strict_sorted_subseq(w_seq, 0, m as int));
                        assert(w_seq[k] >= w_seq[j]);
                        assert(w_seq[j] > v_seq[i]); // follows from if-condition
                        assert(w_seq[k] > v_seq[i]);
                    }
                }
            }
            return false;
        } else {
            // w_seq[j] == v_seq[i], so v[i] is found
            proof {
                assert(w_seq[j] == v_seq[i]);
                assert(w_seq.subrange(0, m as int).contains(v_seq[i]));
                assert forall|k_int: int| 0 <= k_int < i + 1 implies w_seq.subrange(0, m as int).contains(v_seq[k_int]) by {
                    if (k_int < i) {
                        assert(w_seq.subrange(0, m as int).contains(v_seq[k_int])); // from outer invariant
                    } else { // k_int == i
                        assert(w_seq.subrange(0, m as int).contains(v_seq[i])); // proved above
                    }
                }
            }
            j = j + 1; // Move pointer in w past the found element
            i = i + 1; // Move to the next element in v
        }
    }

    // All elements v[0..n-1] have been found in w
    assert(forall|k: int| 0 <= k < n ==> w_seq.subrange(0, m as int).contains(v_seq[k]));
    true
}
// </vc-code>

fn main() {}

}