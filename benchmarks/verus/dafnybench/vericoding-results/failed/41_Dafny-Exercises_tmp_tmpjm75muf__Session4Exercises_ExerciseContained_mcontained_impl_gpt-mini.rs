use vstd::prelude::*;

verus! {

spec fn strict_sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] < s[w]
}

// <vc-helpers>
// <vc-helpers>
// Helper lemma: an element at index `idx` of `s` is contained in `s.subrange(0, m)` when 0 <= idx < m.
proof fn seq_subrange_contains<T>(s: Seq<T>, m: int, idx: int)
    requires
        0 <= idx,
        idx < m,
        0 <= m,
        m <= s.len(),
    ensures
        s.subrange(0, m).contains(s@[(idx)])
{
    // Provide witness k = idx to show membership in the subrange
    assert(exists|k: int| k == idx && 0 <= k && k < m && s@[(k)] == s@[(idx)]);
    assert(s.subrange(0, m).contains(s@[(idx)]));
}
// </vc-helpers>
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
    let mut i: usize = 0;
    let mut j: usize = 0;
    while j < m && i < n
        invariant
            i <= n,
            j <= m,
            // All processed v indices are contained in w[0..m)
            forall|p: int| 0 <= p && p < (i as int) ==> w@.subrange(0, m as int).contains(v@[(p)]),
            // All w indices before j are strictly less than current v[i] (when i < n)
            (i < n) ==> forall|t: int| 0 <= t && t < (j as int) ==> w@[(t)] < v@[(i as int)],
        decreases (m - j) + (n - i)
    {
        // inside loop: j < m && i < n
        let vi: i32 = v[i];
        let wj: i32 = w[j];

        if vi == wj {
            // We found v[i] at w[j]; record containment for index i
            // First, show w.subrange(0,m) contains v@[i]
            proof {
                // j < m, so we can apply lemma with idx = j
                seq_subrange_contains(w@, m as int, j as int);
                // Relate slice values to sequence values
                assert(v@[(i as int)] == vi);
                assert(w@[(j as int)] == wj);
                // Now w.subrange(0,m) contains w@[j], and w@[j] == v@[i], so v@[i] is contained
                assert(w@.subrange(0, m as int).contains(w@[(j as int)]));
                assert(w@[(j as int)] == v@[(i as int)]);
                // From contains of w@[j] and equality, deduce contains of v@[i]
                assert(w@.subrange(0, m as int).contains(v@[(i as int)]));
            }
            // Update pointers: move past matched elements
            i = i + 1;
            j = j + 1;
        } else if vi > wj {
            // Advance w pointer to try to find vi
            j = j + 1;
        } else {
            // vi < wj: since all w[t] for t < j are < vi (by invariant),
            // and current w[j] > vi, vi cannot be in w[0..m)
            return false;
        }
    }

    // After loop, either i == n (all v[0..n) found) or j == m (exhausted w)
    proof {
        if i == n {
            // From invariant: all p < i are contained; with i == n this gives forall p < n
            assert(forall|k: int| 0 <= k && k < n ==> w@.subrange(0, m as int).contains(v@[k]));
        } else {
            // i < n and loop exited, so j == m
            assert(i < n);
            assert(j == m);
            // From invariant with i < n: forall t < j w@[t] < v@[i]; since j == m, this holds for all t < m
            assert(forall|t: int| 0 <= t && t < (m as int) ==> w@[(t)] < v@[(i as int)]);
            // Therefore no w element in 0..m equals v@[i], so v@[i] is not contained
            assert(! (w@.subrange(0, m as int).contains(v@[(i as int)])));
            // Hence not all 0 <= k < n elements of v are contained (take k = i)
            assert(!(forall|k: int| 0 <= k && k < n ==> w@.subrange(0, m as int).contains(v@[k])));
        }
    }

    i == n
}
// </vc-code>

fn main() {}

}