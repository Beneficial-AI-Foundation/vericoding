use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function to check if entire array is sorted
spec fn sorted(a: Vec<int>) -> bool {
    sorted_between(a, 0, a.len() as int)
}

// Predicate to check if array is sorted between indices
spec fn sorted_between(a: Vec<int>, from: int, to: int) -> bool 
    recommends 
        0 <= from <= to,
        to <= a.len()
{
    forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
}

// Spec function to get multiset from vector
spec fn to_multiset(a: Vec<int>) -> Multiset<int> {
    a.to_multiset()
}

// Method to perform bubble sort
fn bubble_sort(a: &mut Vec<int>)
    requires 
        a.len() > 0
    ensures 
        sorted(*a),
        to_multiset(*a) == to_multiset(*old(a))
{
    let n = a.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            a.len() == n,
            to_multiset(*a) == to_multiset(*old(a)),
            // Elements from n-i to n-1 are in their final sorted positions
            sorted_between(*a, (n - i) as int, n as int),
            // Each element in the sorted suffix is >= all elements in the unsorted prefix
            forall|k: int, l: int| 0 <= k < (n - i) as int && (n - i) as int <= l < n as int ==> a[k] <= a[l]
    {
        if i < n - 1 {
            let mut j: usize = 0;
            let limit = n - 1 - i;
            
            while j < limit
                invariant
                    j <= limit,
                    limit == n - 1 - i,
                    i < n,
                    a.len() == n,
                    to_multiset(*a) == to_multiset(*old(a)),
                    // Elements from n-i to n-1 remain in sorted positions
                    sorted_between(*a, (n - i) as int, n as int),
                    // Each element in sorted suffix >= all elements in unsorted prefix
                    forall|k: int, l: int| 0 <= k < (n - i) as int && (n - i) as int <= l < n as int ==> a[k] <= a[l],
                    // Maximum element in processed portion
                    forall|k: int| 0 <= k <= j as int ==> a[k] <= a[j as int]
            {
                if a[j] > a[j + 1] {
                    // Swap elements using temporary variable
                    let temp = a[j];
                    let val_j_plus_1 = a[j + 1];
                    a.set(j, val_j_plus_1);
                    a.set(j + 1, temp);
                }
                j += 1;
            }
        }
        
        i += 1;
    }
}

}