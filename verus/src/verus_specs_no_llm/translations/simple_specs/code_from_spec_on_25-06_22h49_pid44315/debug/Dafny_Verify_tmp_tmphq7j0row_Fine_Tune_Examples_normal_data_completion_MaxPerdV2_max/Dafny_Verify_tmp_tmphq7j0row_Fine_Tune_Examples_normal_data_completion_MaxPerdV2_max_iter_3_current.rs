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
    let mut i: usize = 1;
    
    while (i as int) < n
        invariant
            1 <= i <= n,
            i <= a.len(),
            // max_val is one of the elements we've seen so far
            exists|j: int| 0 <= j < i && a[j as int] == max_val,
            // max_val is >= all elements we've seen so far
            forall|j: int| 0 <= j < i ==> a[j as int] <= max_val
    {
        if a[i] > max_val {
            max_val = a[i];
        }
        i += 1;
    }
    
    // Proof that the final state satisfies is_max
    assert(exists|j: int| 0 <= j < n && a[j as int] == max_val);
    assert(forall|j: int| 0 <= j < n ==> a[j as int] <= max_val);
    
    max_val
}

}