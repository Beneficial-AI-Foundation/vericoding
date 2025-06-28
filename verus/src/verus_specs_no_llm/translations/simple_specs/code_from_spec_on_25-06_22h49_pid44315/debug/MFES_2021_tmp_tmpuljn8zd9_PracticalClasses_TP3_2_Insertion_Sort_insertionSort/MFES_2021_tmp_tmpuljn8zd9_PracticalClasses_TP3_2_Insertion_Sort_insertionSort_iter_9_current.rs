use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isSorted(a: &[int], from: nat, to: nat) -> bool
{
    &&& from <= to <= a.len()
    &&& forall|i: int, j: int| from <= i < j < to ==> a[i as nat] <= a[j as nat]
}

// Helper lemma for multiset reasoning
proof fn multiset_swap_lemma(a: &Vec<int>, b: &Vec<int>, pos: usize, val: int)
    requires 
        pos < a.len(),
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() && i != pos ==> a[i as nat] == b[i as nat],
        b[pos] == val,
    ensures a@.to_multiset().insert(val) == b@.to_multiset().insert(a[pos])
{
    // The multiset property follows from the fact that we're only changing one element
    // and the multiset operations account for this change
    assert(a@.to_multiset().remove(a[pos]).insert(val) == b@.to_multiset().remove(a[pos]).insert(val));
}

// Sorts array 'a' using the insertion sort algorithm.
fn insertionSort(a: &mut Vec<int>)
    ensures isSorted(a, 0, a.len()),
    ensures a@.to_multiset() == old(a)@.to_multiset(),
{
    if a.len() <= 1 {
        return;
    }

    let mut i: usize = 1;
    
    while i < a.len()
        invariant 
            1 <= i <= a.len(),
            isSorted(a, 0, i),
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        let key = a[i];
        let mut j = i;
        
        // Find the correct position for key by shifting elements
        while j > 0 && a[j - 1] > key
            invariant
                j <= i < a.len(),
                key == old(a)@[i as int],
                // Elements from j to i are all > key (shifted elements)
                forall|k: int| (j as int) < k <= (i as int) ==> a[k as nat] > key,
                // Elements from 0 to j-1 remain sorted when j > 0
                j == 0 || isSorted(a, 0, j),
                // Elements beyond i are unchanged from the start of outer loop iteration
                forall|k: int| (i as int) < k < a.len() ==> a[k as nat] == old(a)@[k],
                // The sorted portion before j is preserved from outer loop
                forall|k: int| 0 <= k < (j as int) ==> a[k as nat] == (a@)[k],
                // Multiset is preserved (we're just shifting)
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            a[j] = a[j - 1];
            j = j - 1;
        }
        
        // Insert key at position j
        a[j] = key;
        
        // Prove that the first i+1 elements are sorted
        assert(isSorted(a, 0, i + 1));
        
        i = i + 1;
    }
}

}