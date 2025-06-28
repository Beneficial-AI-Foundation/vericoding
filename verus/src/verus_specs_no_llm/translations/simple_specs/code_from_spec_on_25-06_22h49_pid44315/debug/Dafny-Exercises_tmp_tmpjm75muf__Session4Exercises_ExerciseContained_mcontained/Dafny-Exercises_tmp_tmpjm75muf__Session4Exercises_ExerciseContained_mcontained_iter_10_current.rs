use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn strictSorted(s: Seq<int>) -> bool {
    forall |u, w| 0 <= u < w < s.len() ==> s.spec_index(u) < s.spec_index(w)
}

// Helper lemma to reason about strictly sorted sequences
proof fn lemma_strict_sorted_transitive(s: Seq<int>, i: int, j: int, k: int)
    requires
        strictSorted(s),
        0 <= i <= j <= k < s.len(),
    ensures
        i < k ==> s.spec_index(i) < s.spec_index(k),
        i < j ==> s.spec_index(i) < s.spec_index(j),
        j < k ==> s.spec_index(j) < s.spec_index(k),
{
    // The strictSorted property directly gives us what we need
}

// Helper lemma for subrange membership
proof fn lemma_subrange_membership(s: Seq<int>, elem: int, idx: int, len: int)
    requires
        0 <= idx < len <= s.len(),
        s.spec_index(idx) == elem,
    ensures
        elem in s.subrange(0, len),
{
    // By definition of subrange and membership
}

fn mcontained(v: Vec<int>, w: Vec<int>, n: usize, m: usize) -> (b: bool)
    requires
        n <= m,
        strictSorted(v@),
        strictSorted(w@),
        v.len() >= n && w.len() >= m
    ensures
        b == (forall |k: int| 0 <= k < n ==> v@.spec_index(k) in w@.subrange(0, m as int))
{
    if n == 0 {
        return true;
    }
    
    let mut i: usize = 0; // index for v
    let mut j: usize = 0; // index for w
    
    while i < n && j < m
        invariant
            0 <= i <= n,
            0 <= j <= m,
            n <= v.len(),
            m <= w.len(),
            strictSorted(v@),
            strictSorted(w@),
            // All elements v[0..i] have been found in w[0..m]
            forall |k: int| 0 <= k < i ==> v@.spec_index(k) in w@.subrange(0, m as int),
            // If i < n, then v[i] > all elements in w[0..j]
            i < n ==> forall |l: int| 0 <= l < j ==> w@.spec_index(l) < v@.spec_index(i as int),
    {
        if v[i] == w[j] {
            // Found v[i] in w, move both pointers
            proof {
                // v[i] is now in w[0..m] since j < m
                lemma_subrange_membership(w@, v[i] as int, j as int, m as int);
            }
            i += 1;
            j += 1;
        } else if v[i] > w[j] {
            // v[i] might be found later in w, advance j
            j += 1;
        } else {
            // v[i] < w[j], but w is sorted so v[i] cannot be found in w[j..m]
            proof {
                let vi = v@.spec_index(i as int);
                let wj = w@.spec_index(j as int);
                assert(vi < wj);
                
                // Since w is sorted, for any idx > j, w[idx] > w[j] > v[i]
                assert(forall |idx: int| j < idx < m ==> wj < w@.spec_index(idx)) by {
                    assert(forall |u, v_idx| 0 <= u < v_idx < w@.len() ==> w@.spec_index(u) < w@.spec_index(v_idx));
                }
                
                // v[i] is also not in w[0..j] by invariant
                assert(forall |l: int| 0 <= l < j ==> w@.spec_index(l) < vi);
                
                // Therefore v[i] is not in w[0..m]
                assert(forall |l: int| 0 <= l < m ==> w@.spec_index(l) != vi) by {
                    if j < m {
                        assert(wj == w@.spec_index(j as int));
                        assert(forall |l: int| j < l < m ==> wj < w@.spec_index(l));
                        assert(forall |l: int| j < l < m ==> vi < w@.spec_index(l));
                    }
                }
                
                assert(!(vi in w@.subrange(0, m as int)));
            }
            return false;
        }
    }
    
    // Check if we've processed all elements of v
    if i == n {
        proof {
            // We've found all elements v[0..n] in w[0..m]
            assert(forall |k: int| 0 <= k < n ==> v@.spec_index(k) in w@.subrange(0, m as int));
        }
        return true;
    } else {
        proof {
            // i < n and j == m, so we couldn't find v[i] in w[0..m]
            assert(i < n);
            assert(j == m);
            let vi = v@.spec_index(i as int);
            // By invariant, all w[0..j] = w[0..m] are < v[i], so v[i] is not in w[0..m]
            assert(forall |l: int| 0 <= l < m ==> w@.spec_index(l) < vi);
            assert(forall |l: int| 0 <= l < m ==> w@.spec_index(l) != vi);
            assert(!(vi in w@.subrange(0, m as int)));
            assert(!(forall |k: int| 0 <= k < n ==> v@.spec_index(k) in w@.subrange(0, m as int)));
        }
        return false;
    }
}

}