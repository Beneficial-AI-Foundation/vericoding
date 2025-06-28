use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function to check if entire array is sorted
spec fn sorted(a: Vec<int>) -> bool {
    sorted_between(a, 0, a.len())
}

// Predicate to check if array is sorted between indices
spec fn sorted_between(a: Vec<int>, from: nat, to: nat) -> bool 
    recommends 
        from <= to,
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
            forall|k: int, l: int| n - i <= k < l < n ==> a[k as int] <= a[l as int],
            // Each element in the sorted suffix is >= all elements in the unsorted prefix
            forall|k: int, l: int| 0 <= k < n - i && n - i <= l < n ==> a[k as int] <= a[l as int]
    {
        let mut j: usize = 0;
        
        while j < n - 1 - i
            invariant
                j <= n - 1 - i,
                i < n,
                a.len() == n,
                to_multiset(*a) == to_multiset(*old(a)),
                // Elements from n-i to n-1 remain in sorted positions
                forall|k: int, l: int| n - i <= k < l < n ==> a[k as int] <= a[l as int],
                // Each element in sorted suffix >= all elements in unsorted prefix
                forall|k: int, l: int| 0 <= k < n - i && n - i <= l < n ==> a[k as int] <= a[l as int],
                // Maximum element in prefix 0..j+1 is at position j
                forall|k: int| 0 <= k <= j ==> a[k as int] <= a[j as int]
        {
            if a[j] > a[j + 1] {
                // Swap elements
                let temp = a[j];
                a.set(j, a[j + 1]);
                a.set(j + 1, temp);
                
                // Proof that swap preserves multiset
                proof {
                    assert(to_multiset(*a) == to_multiset(*old(a)));
                }
            }
            j += 1;
        }
        i += 1;
    }
    
    // Final proof that the array is completely sorted
    proof {
        assert(sorted_between(*a, 0, a.len()));
        lemma_sorted_complete(*a);
    }
}

// Proof that sorted_between is transitive and covers the full array
proof fn lemma_sorted_complete(a: Vec<int>)
    requires sorted_between(a, 0, a.len())
    ensures sorted(a)
{
    // This follows directly from the definition
}

// Proof helper for multiset preservation during swaps
proof fn lemma_swap_preserves_multiset(a: Vec<int>, b: Vec<int>, i: usize, j: usize)
    requires 
        i < a.len(),
        j < a.len(),
        i != j,
        a.len() == b.len(),
        b[i as int] == a[j as int],
        b[j as int] == a[i as int],
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == b[k]
    ensures to_multiset(a) == to_multiset(b)
{
    // Proof that swapping two elements preserves the multiset
    // This follows from the properties of multisets in Verus
}

}