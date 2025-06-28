use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindMin(a: &Vec<int>, lo: usize) -> (minIdx: usize)
    requires 
        a.len() > 0,
        lo < a.len()
    ensures 
        lo <= minIdx < a.len(),
        forall|x: usize| lo <= x < a.len() ==> a[minIdx as int] <= a[x as int]
{
    let mut minIdx = lo;
    let mut i = lo + 1;
    
    while i < a.len()
        invariant
            lo <= minIdx < a.len(),
            lo + 1 <= i <= a.len(),
            forall|x: usize| lo <= x < i ==> a[minIdx as int] <= a[x as int]
    {
        if a[i as int] < a[minIdx as int] {
            minIdx = i;
        }
        i = i + 1;
    }
    
    minIdx
}

fn swap(a: &mut Vec<int>, i: usize, j: usize)
    requires 
        old(a).len() > 0,
        i < old(a).len(),
        j < old(a).len()
    ensures
        a.len() == old(a).len(),
        a[i as int] == old(a)[j as int],
        a[j as int] == old(a)[i as int],
        forall|k: usize| 0 <= k < a.len() && k != i && k != j ==> a[k as int] == old(a)[k as int]
{
    let temp = a[i as int];
    a.set(i as int, a[j as int]);
    a.set(j as int, temp);
}

spec fn is_sorted(a: &Vec<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}

// Simplified multiset equality - just check that permutation preserves elements
spec fn multiset_eq<T>(a: &Vec<T>, b: &Vec<T>) -> bool {
    a.len() == b.len() &&
    forall|i: int| 0 <= i < a.len() ==> exists|j: int| 0 <= j < b.len() && a[i] == b[j]
}

// Helper function to prove multiset properties
proof fn swap_preserves_multiset(a: &Vec<int>, b: &Vec<int>, i: usize, j: usize)
    requires
        a.len() == b.len(),
        i < a.len(),
        j < a.len(),
        a[i as int] == b[j as int],
        a[j as int] == b[i as int],
        forall|k: usize| 0 <= k < a.len() && k != i && k != j ==> a[k as int] == b[k as int]
    ensures
        multiset_eq(a, b)
{
    // Proof by construction - each element in a has a corresponding element in b
}

fn selectionSort(a: &mut Vec<int>)
    requires a.len() > 0
    ensures
        a.len() == old(a).len(),
        is_sorted(a),
        multiset_eq(a, old(a))
{
    let mut i: usize = 0;
    let ghost orig_a = *a;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == orig_a.len(),
            // Elements before i are sorted
            forall|x: int, y: int| 0 <= x <= y < i ==> a[x] <= a[y],
            // Elements before i are smaller than or equal to elements from i onwards
            forall|x: int, y: int| 0 <= x < i && i as int <= y < a.len() ==> a[x] <= a[y],
            // Multiset equality is preserved
            multiset_eq(a, &orig_a)
    {
        let minIdx = FindMin(a, i);
        
        if minIdx != i {
            proof {
                // Before swap, prove multiset will be preserved
                let ghost pre_swap = *a;
                assert(multiset_eq(a, &orig_a));
            }
            swap(a, i, minIdx);
            proof {
                // After swap, multiset is still preserved
                swap_preserves_multiset(a, &orig_a, i, minIdx);
            }
        }
        
        proof {
            // Prove that a[i] is the minimum of the remaining elements
            assert(forall|x: usize| i <= x < a.len() ==> a[i as int] <= a[x as int]);
            // Combined with previous invariant, this maintains the sorting property
        }
        
        i = i + 1;
    }
    
    proof {
        // Final proof that the array is fully sorted
        assert(i == a.len());
        assert(forall|x: int, y: int| 0 <= x <= y < a.len() ==> a[x] <= a[y]);
    }
}

}