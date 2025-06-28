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
    
    while i < n
        invariant
            1 <= i <= n,
            i <= a.len(),
            (forall|j: int| 0 <= j && j < i ==> a.spec_index(j) >= min_val),
            (exists|k: int| 0 <= k && k < i && a.spec_index(k) == min_val)
    {
        if a[i] < min_val {
            min_val = a[i];
            // Prove that the new min_val maintains the invariant
            assert(a.spec_index(i as int) == min_val);
            assert(forall|j: int| 0 <= j && j < i ==> a.spec_index(j) >= min_val);
        } else {
            // Prove that min_val is still the minimum after checking a[i]
            assert(a.spec_index(i as int) >= min_val);
        }
        
        i = i + 1;
    }
    
    // After the loop, i == n, so we need to prove the postconditions
    assert(i == n);
    assert(forall|j: int| 0 <= j && j < n ==> a.spec_index(j) >= min_val);
    assert(exists|k: int| 0 <= k && k < n && a.spec_index(k) == min_val);
    
    min_val
}

}