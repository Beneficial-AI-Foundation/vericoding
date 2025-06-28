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
spec fn sorted_between(a: Vec<int>, from: int, to: int) -> bool {
    &&& 0 <= from <= to
    &&& to <= a.len()
    &&& forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
}

// Spec function to get multiset from vector
spec fn to_multiset(a: Vec<int>) -> Multiset<int> {
    a.to_multiset()
}

// Helper lemma for multiset preservation during swaps
proof fn lemma_swap_preserves_multiset(a: Vec<int>, i: usize, j: usize, new_a: Vec<int>)
    requires
        i < a.len(),
        j < a.len(),
        i != j,
        new_a.len() == a.len(),
        new_a[i as int] == a[j as int],
        new_a[j as int] == a[i as int],
        forall|k: int| 0 <= k < a.len() && k != i as int && k != j as int ==> new_a[k] == a[k]
    ensures
        new_a.to_multiset() == a.to_multiset()
{
    // Verus can prove multiset equality after swap
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
            // Elements from n-i to n-1 are sorted and in final position
            sorted_between(*a, (n - i) as int, n as int),
            // All elements in sorted part are >= elements in unsorted part
            forall|k: int, l: int| 0 <= k < (n - i) as int && (n - i) as int <= l < n as int ==> a[k] <= a[l]
        decreases n - i
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
                    // Sorted suffix is preserved
                    sorted_between(*a, (n - i) as int, n as int),
                    // Separation property maintained
                    forall|k: int, l: int| 0 <= k < (n - i) as int && (n - i) as int <= l < n as int ==> a[k] <= a[l],
                    // Largest element so far is bubbled up
                    forall|k: int| 0 <= k <= j as int ==> a[k] <= a[j as int]
                decreases limit - j
            {
                if a[j] > a[j + 1] {
                    // Capture old state for proof
                    let old_a = *a;
                    
                    // Perform swap using indexing
                    let temp = a[j];
                    a[j] = a[j + 1];
                    a[j + 1] = temp;
                    
                    // Prove multiset preservation
                    proof {
                        lemma_swap_preserves_multiset(old_a, j, j + 1, *a);
                    }
                }
                
                j += 1;
            }
        }
        
        i += 1;
    }
}

}