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
    Multiset::from_seq(a@)
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
        to_multiset(new_a) == to_multiset(a)
{
    assert(new_a@ =~= a@.update(i as int, a[j as int]).update(j as int, a[i as int]));
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
        if i == 0 {
            // First iteration - no sorted suffix yet, just establish basic properties
            let mut j: usize = 0;
            let limit = n - 1;
            
            while j < limit
                invariant
                    j <= limit,
                    limit == n - 1,
                    a.len() == n,
                    to_multiset(*a) == to_multiset(*old(a)),
                    // The maximum element up to position j is at position j
                    forall|k: int| 0 <= k <= j as int ==> a[k] <= a[j as int]
                decreases limit - j
            {
                if a[j] > a[j + 1] {
                    // Capture old state for proof
                    let ghost old_inner_a = *a;
                    
                    // Perform swap
                    let temp = a[j];
                    a[j] = a[j + 1];
                    a[j + 1] = temp;
                    
                    // Prove multiset preservation
                    proof {
                        lemma_swap_preserves_multiset(old_inner_a, j, j + 1, *a);
                    }
                }
                
                j += 1;
            }
            
            // After first pass, the maximum is at the end
            proof {
                assert(forall|k: int| 0 <= k < (n - 1) as int ==> a[k] <= a[(n - 1) as int]);
                assert(sorted_between(*a, (n - 1) as int, n as int));
            }
            
        } else if i < n - 1 {
            let mut j: usize = 0;
            let limit = n - 1 - i;
            
            // Store the old state before inner loop
            let ghost old_outer_a = *a;
            
            while j < limit
                invariant
                    j <= limit,
                    limit == n - 1 - i,
                    i < n,
                    a.len() == n,
                    to_multiset(*a) == to_multiset(old_outer_a),
                    to_multiset(old_outer_a) == to_multiset(*old(a)),
                    // Sorted suffix is preserved
                    sorted_between(*a, (n - i) as int, n as int),
                    forall|k: int| (n - i) as int <= k < n as int ==> a[k] == old_outer_a[k],
                    // Separation property maintained
                    forall|k: int, l: int| 0 <= k < (n - i) as int && (n - i) as int <= l < n as int ==> a[k] <= a[l],
                    // Largest element so far is bubbled up
                    forall|k: int| 0 <= k <= j as int ==> a[k] <= a[j as int]
                decreases limit - j
            {
                if a[j] > a[j + 1] {
                    // Capture old state for proof
                    let ghost old_inner_a = *a;
                    
                    // Perform swap
                    let temp = a[j];
                    a[j] = a[j + 1];
                    a[j + 1] = temp;
                    
                    // Prove multiset preservation
                    proof {
                        lemma_swap_preserves_multiset(old_inner_a, j, j + 1, *a);
                    }
                }
                
                j += 1;
            }
            
            // After inner loop, extend the sorted region
            proof {
                assert(forall|k: int| 0 <= k < (n - i - 1) as int ==> a[k] <= a[(n - i - 1) as int]);
                assert(a[(n - i - 1) as int] <= a[(n - i) as int]); // Due to separation property
                assert(sorted_between(*a, (n - i - 1) as int, n as int));
            }
        }
        
        i += 1;
    }
    
    // Final proof that the entire array is sorted
    proof {
        assert(i == n);
        assert((n - i) as int == 0);
        assert(sorted_between(*a, 0, n as int));
        assert(sorted(*a));
    }
}

}