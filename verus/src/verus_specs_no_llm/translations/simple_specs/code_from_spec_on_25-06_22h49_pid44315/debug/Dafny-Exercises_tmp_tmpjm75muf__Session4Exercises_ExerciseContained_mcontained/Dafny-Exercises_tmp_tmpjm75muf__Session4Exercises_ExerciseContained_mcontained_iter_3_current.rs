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
                assert(w@.spec_index(j as int) in w@.subrange(0, m as int));
                assert(v@.spec_index(i as int) in w@.subrange(0, m as int));
                
                // Maintain invariant: all elements w[0..j+1] are < v[i+1] (if i+1 < n)
                if i + 1 < n {
                    assert(strictSorted(v@));
                    assert(v@.spec_index(i as int) < v@.spec_index((i + 1) as int));
                    assert(forall |l: int| 0 <= l <= j ==> w@.spec_index(l) <= w@.spec_index(j as int));
                    assert(forall |l: int| 0 <= l <= j ==> w@.spec_index(l) < v@.spec_index((i + 1) as int));
                }
            }
            i += 1;
            j += 1;
        } else if v[i] > w[j] {
            // v[i] might be found later in w, advance j
            proof {
                // Maintain invariant that w[0..j+1] are all < v[i]
                assert(w@.spec_index(j as int) < v@.spec_index(i as int));
                assert(forall |l: int| 0 <= l < j ==> w@.spec_index(l) < v@.spec_index(i as int));
                assert(forall |l: int| 0 <= l < j + 1 ==> w@.spec_index(l) < v@.spec_index(i as int));
            }
            j += 1;
        } else {
            // v[i] < w[j], but w is sorted so v[i] cannot be found in w[j..m]
            proof {
                assert(v@.spec_index(i as int) < w@.spec_index(j as int));
                assert(strictSorted(w@));
                assert(forall |l: int| j <= l < m ==> w@.spec_index(j as int) < w@.spec_index(l));
                assert(forall |l: int| j <= l < m ==> v@.spec_index(i as int) < w@.spec_index(l));
                assert(forall |l: int| j <= l < m ==> v@.spec_index(i as int) != w@.spec_index(l));
                
                // v[i] is also not in w[0..j] by invariant
                assert(forall |l: int| 0 <= l < j ==> w@.spec_index(l) < v@.spec_index(i as int));
                assert(forall |l: int| 0 <= l < j ==> v@.spec_index(i as int) != w@.spec_index(l));
                
                // Therefore v[i] is not in w[0..m]
                assert(forall |l: int| 0 <= l < m ==> v@.spec_index(i as int) != w@.spec_index(l));
                assert(!(v@.spec_index(i as int) in w@.subrange(0, m as int)));
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
            assert(forall |l: int| 0 <= l < m ==> v@.spec_index(i as int) != w@.spec_index(l));
            assert(!(v@.spec_index(i as int) in w@.subrange(0, m as int)));
        }
    }
    
    result
}

}