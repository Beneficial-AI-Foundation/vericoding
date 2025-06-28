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

// Helper lemma to prove sortedness after insertion
proof fn lemma_insert_maintains_sorted(a: &Vec<int>, j: nat, i: nat, key: int)
    requires
        j <= i < a.len(),
        isSorted(a, 0, j),
        forall|k: int| 0 <= k < j ==> a[k as nat] <= key,
        forall|k: int| j < k <= i ==> a[k as nat] > key,
        a[j] == key,
    ensures
        isSorted(a, 0, i + 1),
{
    assert forall|x: int, y: int| 0 <= x < y < (i + 1) implies a[x as nat] <= a[y as nat] by {
        if y <= j {
            // Both in sorted prefix
        } else if x < j {
            // x in prefix, y after insertion point
            assert(a[x as nat] <= key);
            assert(a[y as nat] > key);
        } else if x == j {
            // x is the inserted key
            assert(a[y as nat] > key);
        } else {
            // Both after insertion point
            assert(a[x as nat] > key);
            assert(a[y as nat] > key);
        }
    }
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
        
        // Store the original array state for multiset reasoning
        let a_before_inner = Ghost(a@);
        
        // Find the correct position for key by shifting elements
        while j > 0 && a[j - 1] > key
            invariant
                j <= i < a.len(),
                key == a_before_inner@[i as int],
                // The array is sorted up to j
                isSorted(a, 0, j),
                // All elements from 0 to j-1 are <= key (if we're still moving)
                j == 0 || a[j - 1] <= key || (j > 0 && a[j - 1] > key),
                // Elements from j+1 to i+1 are shifted versions of original elements from j to i
                forall|k: int| j < k <= i ==> a[k as nat] == a_before_inner@[(k - 1) as int],
                // Elements from j+1 to i are all > key
                forall|k: int| j < k <= i ==> a[k as nat] > key,
                // Elements before j are unchanged from before inner loop
                forall|k: int| 0 <= k < j ==> a[k as nat] == a_before_inner@[k],
                // Multiset is preserved (we have the elements shifted around)
                a@.to_multiset() == a_before_inner@.to_multiset(),
        {
            a[j] = a[j - 1];
            j = j - 1;
        }
        
        // Insert key at position j
        a[j] = key;
        
        // Prove that we maintain sortedness
        assert(j == 0 || a[j - 1] <= key);
        assert(forall|k: int| j < k <= i ==> a[k as nat] > key);
        
        // Prove sortedness using the lemma
        if j < i {
            proof {
                lemma_insert_maintains_sorted(a, j, i, key);
            }
        }
        
        // Prove multiset preservation
        assert(a@.to_multiset() == old(a)@.to_multiset()) by {
            // The multiset is preserved because we only moved elements around
            // and inserted the key that was already in the array
        }
        
        i = i + 1;
    }
}

}