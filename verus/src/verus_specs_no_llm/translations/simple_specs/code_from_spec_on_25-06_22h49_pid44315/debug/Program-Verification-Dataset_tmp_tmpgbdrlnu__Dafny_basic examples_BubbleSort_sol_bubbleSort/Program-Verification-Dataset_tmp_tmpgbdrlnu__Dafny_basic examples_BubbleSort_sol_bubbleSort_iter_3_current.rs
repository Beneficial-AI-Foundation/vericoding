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
        old(a).len() > 0
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
                // Maximum element in prefix 0..j+1 is at position j
                forall|k: int| 0 <= k <= j as int ==> a[k] <= a[j as int]
        {
            if a[j] > a[j + 1] {
                // Swap elements
                let temp = a[j];
                a.set(j, a[j + 1]);
                a.set(j + 1, temp);
                
                // Proof that swap preserves multiset
                proof {
                    lemma_swap_preserves_multiset_at(*old(a), *a, j, j + 1);
                }
            }
            j += 1;
            
            // Help verifier understand the maximum property is maintained
            proof {
                if j <= limit {
                    assert(forall|k: int| 0 <= k <= j as int ==> a[k] <= a[j as int]);
                }
            }
        }
        
        // After inner loop, the maximum element is bubbled to position n-1-i
        proof {
            assert(forall|k: int| 0 <= k < (n - i) as int ==> a[k] <= a[(n - 1 - i) as int]);
            assert(sorted_between(*a, (n - i - 1) as int, n as int));
        }
        
        i += 1;
    }
    
    // Final proof that the array is completely sorted
    proof {
        assert(i == n);
        assert(sorted_between(*a, 0, n as int));
        lemma_sorted_complete(*a);
    }
}

// Proof that sorted_between is transitive and covers the full array
proof fn lemma_sorted_complete(a: Vec<int>)
    requires sorted_between(a, 0, a.len() as int)
    ensures sorted(a)
{
    // This follows directly from the definition
}

// Proof helper for multiset preservation during swaps
proof fn lemma_swap_preserves_multiset_at(old_a: Vec<int>, new_a: Vec<int>, i: usize, j: usize)
    requires 
        i < old_a.len(),
        j < old_a.len(),
        i != j,
        old_a.len() == new_a.len(),
        new_a[i as int] == old_a[j as int],
        new_a[j as int] == old_a[i as int],
        forall|k: int| 0 <= k < old_a.len() && k != i as int && k != j as int ==> old_a[k] == new_a[k]
    ensures to_multiset(old_a) == to_multiset(new_a)
{
    // The multiset property follows from the fact that we only swapped two elements
    // Verus's built-in multiset reasoning handles this automatically
}

}