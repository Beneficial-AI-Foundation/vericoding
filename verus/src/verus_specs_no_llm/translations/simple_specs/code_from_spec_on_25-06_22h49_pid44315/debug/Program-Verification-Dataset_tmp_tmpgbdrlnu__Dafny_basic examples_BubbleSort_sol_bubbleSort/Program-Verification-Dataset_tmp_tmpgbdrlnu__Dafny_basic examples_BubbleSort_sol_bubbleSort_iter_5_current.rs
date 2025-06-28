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

// Helper lemma for multiset preservation during swaps
proof fn lemma_swap_preserves_multiset(a: &Vec<int>, i: usize, j: usize, val_i: int, val_j: int)
    requires
        i < a.len(),
        j < a.len(),
        i != j,
        a[i as int] == val_i,
        a[j as int] == val_j,
    ensures
        a.update(i, val_j).update(j, val_i).to_multiset() == a.to_multiset()
{
    // Verus can prove this automatically
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
                    // Largest element bubbled to position j
                    forall|k: int| 0 <= k <= j as int ==> a[k] <= a[j as int]
            {
                if a[j] > a[j + 1] {
                    // Perform swap with proof annotation
                    let temp = a[j];
                    let val_j_plus_1 = a[j + 1];
                    
                    // Prove multiset preservation
                    proof {
                        lemma_swap_preserves_multiset(a, j, j + 1, temp, val_j_plus_1);
                    }
                    
                    a.set(j, val_j_plus_1);
                    a.set(j + 1, temp);
                    
                    // Assert properties are maintained after swap
                    assert(a[j] <= a[j + 1]);
                    assert(forall|k: int| 0 <= k <= j as int ==> a[k] <= a[j + 1]);
                }
                j += 1;
            }
            
            // After inner loop, assert that the largest element is in correct position
            assert(forall|k: int| 0 <= k < (n - i) as int ==> a[k] <= a[(n - i - 1) as int]);
            assert(sorted_between(*a, (n - i - 1) as int, n as int));
        }
        
        i += 1;
    }
    
    // Final assertion that the entire array is sorted
    assert(sorted_between(*a, 0, n as int));
}

}