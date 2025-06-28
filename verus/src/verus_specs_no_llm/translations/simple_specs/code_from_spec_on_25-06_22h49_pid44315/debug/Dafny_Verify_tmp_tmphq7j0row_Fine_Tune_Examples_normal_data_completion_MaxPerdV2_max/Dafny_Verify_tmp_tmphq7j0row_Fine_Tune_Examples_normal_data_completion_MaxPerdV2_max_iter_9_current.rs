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
        let old_max_val = max_val;
        
        if a[i as int] > max_val {
            max_val = a[i as int];
        }
        
        // Prove the invariant for the next iteration
        assert(exists|j: int| 0 <= j < i + 1 && a[j as int] == max_val) by {
            if a[i as int] > old_max_val {
                // max_val is now a[i], so witness is i
                assert(a[i as int] == max_val);
                assert(0 <= i < i + 1);
            } else {
                // max_val unchanged, so old witness still works
                assert(max_val == old_max_val);
                assert(exists|j: int| 0 <= j < i && a[j as int] == old_max_val);
            }
        };
        
        assert(forall|j: int| 0 <= j < i + 1 ==> a[j as int] <= max_val) by {
            assert(forall|j: int| 0 <= j < i ==> a[j as int] <= old_max_val);
            if a[i as int] > old_max_val {
                assert(a[i as int] == max_val);
                assert(forall|j: int| 0 <= j < i ==> a[j as int] <= max_val);
            } else {
                assert(a[i as int] <= old_max_val);
                assert(max_val == old_max_val);
                assert(forall|j: int| 0 <= j < i ==> a[j as int] <= max_val);
                assert(a[i as int] <= max_val);
            }
        };
        
        i += 1;
    }
    
    max_val
}

}