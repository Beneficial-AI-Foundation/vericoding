use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn min(a: Vec<int>, n: usize) -> (min: int)
    requires
        0 < n <= a.len()
    ensures
        (exists|i: int| 0 <= i && i < n && a.spec_index(i) == min),
        (forall|i: int| 0 <= i && i < n ==> a.spec_index(i) >= min)
{
    let mut min_val = a[0];
    let mut i: usize = 1;
    let mut min_index: usize = 0;
    
    while i < n
        invariant
            1 <= i <= n,
            i <= a.len(),
            0 <= min_index < i,
            min_index < a.len(),
            a.spec_index(min_index as int) == min_val,
            (forall|j: int| 0 <= j && j < i ==> a.spec_index(j) >= min_val),
            (exists|k: int| 0 <= k && k < i && a.spec_index(k) == min_val)
    {
        if a[i] < min_val {
            min_val = a[i];
            min_index = i;
            
            // Proof that the new minimum is valid
            assert(a.spec_index(i as int) == min_val);
            assert(0 <= i && i < n);
            
            // Proof that all previous elements are >= new minimum
            assert(forall|j: int| 0 <= j && j < i ==> a.spec_index(j) >= min_val) by {
                // This follows from the loop invariant and the fact that min_val is now smaller
            };
        } else {
            // Proof that min_val is still the minimum
            assert(a.spec_index(i as int) >= min_val);
        }
        
        i = i + 1;
        
        // Maintain the invariant that there exists an index with the minimum value
        assert(0 <= min_index && min_index < i - 1);
        assert(a.spec_index(min_index as int) == min_val);
    }
    
    // At this point, i == n, so we've examined all elements from 0 to n-1
    assert(i == n);
    assert(0 <= min_index && min_index < n);
    assert(a.spec_index(min_index as int) == min_val);
    assert(forall|j: int| 0 <= j && j < n ==> a.spec_index(j) >= min_val);
    
    // The postconditions are satisfied
    assert(exists|k: int| 0 <= k && k < n && a.spec_index(k) == min_val) by {
        assert(0 <= min_index && min_index < n && a.spec_index(min_index as int) == min_val);
    };
    
    min_val
}

}