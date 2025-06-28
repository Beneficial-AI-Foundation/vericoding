use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn strictSorted(s: Seq<int>) -> bool {
    forall |u, w| 0 <= u < w < s.len() ==> s.spec_index(u) < s.spec_index(w)
}

fn mcontained(v: Vec<int>, w: Vec<int>, n: usize, m: usize) -> (b: bool)
    requires
        n <= m,
        strictSorted(v@),
        strictSorted(w@),
        v.len() >= n && w.len() >= m
    ensures
        b == forall |k: int| 0 <= k < n ==> v@.spec_index(k) in w@.subrange(0, m as int)
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
                assert(v@.spec_index(i as int) == w@.spec_index(j as int));
                assert(j < m);
                assert(w@.spec_index(j as int) in w@.subrange(0, m as int)) by {
                    assert(0 <= j < m);
                };
                assert(v@.spec_index(i as int) in w@.subrange(0, m as int));
            }
            i += 1;
            j += 1;
        } else if v[i] > w[j] {
            // v[i] might be found later in w, advance j
            j += 1;
        } else {
            // v[i] < w[j], but w is sorted so v[i] cannot be found in w[j..m]
            proof {
                assert(v@.spec_index(i as int) < w@.spec_index(j as int));
                
                // Since w is sorted, all elements w[k] for k >= j are >= w[j]
                // and for k > j are > w[j], so they're all > v[i]
                
                // v[i] is also not in w[0..j] by invariant
                assert(forall |l: int| 0 <= l < j ==> w@.spec_index(l) < v@.spec_index(i as int));
                
                // Therefore v[i] is not in w[0..m]
                assert(forall |idx: int| 0 <= idx < m ==> w@.spec_index(idx) != v@.spec_index(i as int)) by {
                    assert(forall |idx: int| 0 <= idx < m ==> {
                        if idx < j {
                            w@.spec_index(idx) < v@.spec_index(i as int)
                        } else if idx == j {
                            w@.spec_index(idx) > v@.spec_index(i as int)
                        } else {
                            // idx > j, so w[idx] >= w[j] > v[i] by strict sorting
                            w@.spec_index(j as int) < w@.spec_index(idx) && v@.spec_index(i as int) < w@.spec_index(j as int)
                        }
                    });
                };
                
                assert(!(v@.spec_index(i as int) in w@.subrange(0, m as int))) by {
                    assert(forall |idx: int| 0 <= idx < m ==> w@.spec_index(idx) != v@.spec_index(i as int));
                };
            }
            return false;
        }
    }
    
    // Check if we've processed all elements of v
    if i == n {
        proof {
            // We've found all elements v[0..n] in w[0..m]
            assert(forall |k: int| 0 <= k < i ==> v@.spec_index(k) in w@.subrange(0, m as int));
            assert(i == n);
            assert(forall |k: int| 0 <= k < n ==> v@.spec_index(k) in w@.subrange(0, m as int));
        }
        return true;
    } else {
        proof {
            // i < n and j == m, so we couldn't find v[i] in w[0..m]
            assert(i < n);
            assert(j == m);
            // By invariant, all w[0..j] = w[0..m] are < v[i], so v[i] is not in w[0..m]
            assert(forall |l: int| 0 <= l < j ==> w@.spec_index(l) < v@.spec_index(i as int));
            assert(j == m);
            assert(forall |l: int| 0 <= l < m ==> w@.spec_index(l) < v@.spec_index(i as int));
            assert(!(v@.spec_index(i as int) in w@.subrange(0, m as int))) by {
                assert(forall |idx: int| 0 <= idx < m ==> w@.spec_index(idx) < v@.spec_index(i as int));
                assert(forall |idx: int| 0 <= idx < m ==> w@.spec_index(idx) != v@.spec_index(i as int));
            };
            assert(0 <= i < n);
            assert(!(forall |k: int| 0 <= k < n ==> v@.spec_index(k) in w@.subrange(0, m as int)));
        }
        return false;
    }
}

}