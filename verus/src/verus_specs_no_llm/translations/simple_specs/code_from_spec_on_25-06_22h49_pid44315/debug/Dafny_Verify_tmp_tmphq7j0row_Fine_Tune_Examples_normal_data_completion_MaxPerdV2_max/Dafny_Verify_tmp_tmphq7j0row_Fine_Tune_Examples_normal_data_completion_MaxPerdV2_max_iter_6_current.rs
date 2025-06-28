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
        i += 1;
    }
    
    // At this point, i == n, so we've examined all elements from 0 to n-1
    assert(i == n);
    
    // The loop invariant gives us what we need for is_max
    assert(exists|j: int| 0 <= j < i && a[j as int] == max_val);
    assert(forall|j: int| 0 <= j < i ==> a[j as int] <= max_val);
    
    // Since i == n, we have the postcondition
    assert(exists|j: int| 0 <= j < n && a[j as int] == max_val);
    assert(forall|j: int| 0 <= j < n ==> a[j as int] <= max_val);
    
    max_val
}

}