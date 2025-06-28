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

// Helper lemma for proving sorted property after insertion
proof fn insertion_sorted_lemma(a: &Vec<int>, pos: usize, key: int)
    requires
        pos < a.len(),
        isSorted(a, 0, pos),
        pos == 0 || a[pos - 1] <= key,
        forall|k: int| (pos as int) < k < a.len() ==> a[k as nat] >= key,
        a[pos] == key,
    ensures
        isSorted(a, 0, pos + 1)
{
    // The proof follows from the fact that:
    // 1. Elements 0..pos are sorted
    // 2. a[pos-1] <= key (if pos > 0)
    // 3. key <= all elements after pos
    // Therefore 0..pos+1 is sorted
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
        
        // Save the state at the beginning of inner operations
        let ghost old_a_inner = a@;
        
        // Find the correct position for key by shifting elements
        while j > 0 && a[j - 1] > key
            invariant
                j <= i < a.len(),
                key == old_a_inner[i as int],
                // Elements from j to i are all > key (shifted elements)
                forall|k: int| (j as int) < k <= (i as int) ==> a[k as nat] > key,
                // Elements from 0 to j-1 remain sorted
                j == 0 || isSorted(a, 0, j),
                // Elements beyond i are unchanged
                forall|k: int| (i as int) < k < a.len() ==> a[k as nat] == old_a_inner[k],
                // Elements before the shifting area are unchanged
                forall|k: int| 0 <= k < (j as int) ==> a[k as nat] == old_a_inner[k],
                // If j > 0, then a[j-1] <= key (loop condition ensures this)
                j > 0 ==> a[(j-1) as nat] <= key,
                // Multiset is preserved during shifting
                a@.to_multiset() == old_a_inner.to_multiset(),
        {
            a[j] = a[j - 1];
            j = j - 1;
        }
        
        // Insert key at position j
        a[j] = key;
        
        // Prove that the sorted property is maintained
        if j > 0 {
            assert(a[j - 1] <= key);
        }
        
        // Prove elements after j are >= key
        assert(forall|k: int| (j as int) < k <= (i as int) ==> a[k as nat] >= key);
        
        // Use the helper lemma to prove sorting
        insertion_sorted_lemma(a, j, key);
        
        // The sorted property extends to i+1
        assert(isSorted(a, 0, i + 1));
        
        i = i + 1;
    }
}

}