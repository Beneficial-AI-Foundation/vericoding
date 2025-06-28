use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_max(max: int, a: Vec<int>, n: int) -> bool {
    // max must be one of the elements in the first n positions
    (exists|i: int| 0 <= i < n && a[i as int] == max) &&
    // max must be >= all elements in the first n positions
    (forall|i: int| 0 <= i < n ==> a[i as int] <= max)
}

fn max(a: Vec<int>, n: int) -> (max: int)
    requires
        0 < n <= a.len()
    ensures
        is_max(max, a, n)
{
    let mut max_val = a[0];
    let mut i: int = 1;
    
    while i < n
        invariant
            1 <= i <= n,
            i <= a.len(),
            // max_val is one of the elements we've seen so far
            exists|j: int| 0 <= j < i && a[j as int] == max_val,
            // max_val is >= all elements we've seen so far
            forall|j: int| 0 <= j < i ==> a[j as int] <= max_val
    {
        if a[i as int] > max_val {
            max_val = a[i as int];
        }
        
        // Prove the invariant for the next iteration
        assert(exists|j: int| 0 <= j < i + 1 && a[j as int] == max_val) by {
            if a[i as int] > max_val {
                // This case is impossible since we just updated max_val
                assert(false);
            } else {
                // max_val was either unchanged or became a[i]
                if a[i as int] == max_val {
                    // The current element equals max_val
                    assert(0 <= i < i + 1);
                } else {
                    // max_val was unchanged, so the old witness still works
                    assert(exists|j: int| 0 <= j < i && a[j as int] == max_val);
                }
            }
        };
        
        assert(forall|j: int| 0 <= j < i + 1 ==> a[j as int] <= max_val) by {
            // For all j < i, we already know a[j] <= old max_val <= new max_val
            assert(forall|j: int| 0 <= j < i ==> a[j as int] <= max_val);
            // For j == i, either a[i] > old max_val (so max_val = a[i]) or a[i] <= max_val
            assert(a[i as int] <= max_val);
        };
        
        i += 1;
    }
    
    // At this point, i == n, so we need to prove is_max(max_val, a, n)
    assert(exists|j: int| 0 <= j < n && a[j as int] == max_val);
    assert(forall|j: int| 0 <= j < n ==> a[j as int] <= max_val);
    
    max_val
}

}