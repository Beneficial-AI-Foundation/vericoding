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
                
                // Maintain invariant for next iteration
                if i + 1 < n {
                    // Show that all w[0..j+1] are < v[i+1]
                    assert(v@.spec_index(i as int) < v@.spec_index((i + 1) as int)) by {
                        assert(strictSorted(v@));
                        assert(i < (i + 1) < v@.len());
                    };
                    
                    // All previous elements w[0..j] are < v[i] = w[j]
                    assert(forall |l: int| 0 <= l < j ==> w@.spec_index(l) < w@.spec_index(j as int)) by {
                        assert(strictSorted(w@));
                    };
                    
                    // Therefore all w[0..j+1] are < v[i+1]
                    assert(forall |l: int| 0 <= l < j + 1 ==> w@.spec_index(l) < v@.spec_index((i + 1) as int)) by {
                        assert(forall |l: int| 0 <= l < j ==> w@.spec_index(l) < v@.spec_index(i as int));
                        assert(w@.spec_index(j as int) == v@.spec_index(i as int));
                        assert(v@.spec_index(i as int) < v@.spec_index((i + 1) as int));
                    };
                }
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
                
                // Since w is sorted, all w[j..m] are >= w[j] > v[i]
                assert(forall |l: int| j <= l < m ==> w@.spec_index(j as int) <= w@.spec_index(l)) by {
                    assert(strictSorted(w@));
                };
                
                // v[i] is also not in w[0..j] by invariant
                assert(forall |l: int| 0 <= l < j ==> w@.spec_index(l) < v@.spec_index(i as int));
                
                // Therefore v[i] is not in w[0..m]
                assert(!(v@.spec_index(i as int) in w@.subrange(0, m as int))) by {
                    if v@.spec_index(i as int) in w@.subrange(0, m as int) {
                        let witness_idx = choose |idx: int| 0 <= idx < m && w@.spec_index(idx) == v@.spec_index(i as int);
                        if witness_idx < j {
                            assert(w@.spec_index(witness_idx) < v@.spec_index(i as int)); // contradiction
                        } else {
                            assert(w@.spec_index(j as int) <= w@.spec_index(witness_idx));
                            assert(v@.spec_index(i as int) < w@.spec_index(j as int)); // contradiction
                        }
                    }
                };
            }
            return false;
        }
    }
    
    // Check if we've processed all elements of v
    let result = i == n;
    
    proof {
        if result {
            // We've found all elements v[0..n] in w[0..m]
            assert(i == n);
            assert(forall |k: int| 0 <= k < n ==> v@.spec_index(k) in w@.subrange(0, m as int));
        } else {
            // i < n and j == m, so v[i] was not found in w[0..m]
            assert(i < n);
            assert(j == m);
            assert(forall |l: int| 0 <= l < m ==> w@.spec_index(l) < v@.spec_index(i as int));
            assert(!(v@.spec_index(i as int) in w@.subrange(0, m as int))) by {
                if v@.spec_index(i as int) in w@.subrange(0, m as int) {
                    let witness_idx = choose |idx: int| 0 <= idx < m && w@.spec_index(idx) == v@.spec_index(i as int);
                    assert(w@.spec_index(witness_idx) < v@.spec_index(i as int)); // contradiction
                }
            };
        }
    }
    
    result
}

}