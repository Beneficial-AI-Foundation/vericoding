use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn findMax(a: Vec<int>, n: int) -> (r: int)
    requires
        a.len() > 0,
        0 < n <= a.len()
    ensures
        0 <= r < n <= a.len(),
        forall|k: int| 0 <= k < n ==> a.spec_index(r) >= a.spec_index(k),
{
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    let n_usize = n as usize;
    
    while i < n_usize
        invariant
            0 < n <= a.len(),
            n_usize == n as usize,
            1 <= i <= n_usize,
            0 <= max_idx < i,
            max_idx < n_usize,
            forall|k: int| 0 <= k < i ==> a.spec_index(max_idx as int) >= a.spec_index(k),
    {
        // Prove array access is safe
        assert(i < n_usize);
        assert(n_usize <= a.len());
        assert(i < a.len());
        assert(max_idx < a.len());
        
        if a[i] > a[max_idx] {
            max_idx = i;
        }
        
        i += 1;
        
        // Help prove the invariant is maintained
        assert(forall|k: int| 0 <= k < i ==> a.spec_index(max_idx as int) >= a.spec_index(k)) by {
            assert(forall|k: int| 0 <= k < i - 1 ==> a.spec_index(max_idx as int) >= a.spec_index(k));
            if max_idx == i - 1 {
                assert(a.spec_index(max_idx as int) >= a.spec_index((i - 1) as int));
            } else {
                assert(a.spec_index(max_idx as int) >= a.spec_index((i - 1) as int));
            }
        };
    }
    
    // Final proof assertions
    assert(i == n_usize);
    assert(n_usize == n as usize);
    assert(forall|k: int| 0 <= k < n ==> a.spec_index(max_idx as int) >= a.spec_index(k)) by {
        assert(forall|k: int| 0 <= k < i ==> a.spec_index(max_idx as int) >= a.spec_index(k));
        assert(i as int == n);
    };
    assert(0 <= max_idx as int < n) by {
        assert(max_idx < n_usize);
        assert(n_usize == n as usize);
        assert(max_idx as int < n);
    };
    
    max_idx as int
}

}