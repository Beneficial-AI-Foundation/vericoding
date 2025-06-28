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
                // The array is sorted up to the insertion point
                isSorted(a, 0, j),
                // Elements from j to i are all > key (shifted elements)
                forall|k: int| j < k <= i ==> a[k as nat] > key,
                // Elements before j are <= key or we haven't checked yet
                j == 0 || a[j - 1] <= key || (j > 0 && a[j - 1] > key),
                // Multiset is preserved except for the temporary displacement
                a@.to_multiset().remove(key) == old(a)@.to_multiset().remove(key),
                a@.to_multiset().count(key) == old(a)@.to_multiset().count(key),
        {
            a[j] = a[j - 1];
            j = j - 1;
        }
        
        // Insert key at position j
        a[j] = key;
        
        // Prove that sortedness is maintained after insertion
        assert(isSorted(a, 0, i + 1)) by {
            // After inserting key at position j:
            // 1. Elements 0..j are sorted and <= key
            // 2. Element at j is key
            // 3. Elements j+1..i+1 are sorted and > key
            assert(j == 0 || a[j - 1] <= key);
            assert(forall|k: int| j < k <= i ==> a[k as nat] >= key);
            
            // Prove all pairs are in order
            assert forall|x: int, y: int| 0 <= x < y < (i + 1) implies a[x as nat] <= a[y as nat] by {
                if x < j && y < j {
                    // Both in the sorted prefix before insertion point
                    assert(isSorted(a, 0, j));
                } else if x < j && y == j {
                    // x before insertion, y is the key
                    assert(a[x as nat] <= key);
                } else if x < j && y > j {
                    // x before insertion, y after insertion
                    assert(a[x as nat] <= key);
                    assert(a[y as nat] >= key);
                } else if x == j && y > j {
                    // x is the key, y after insertion
                    assert(a[y as nat] >= key);
                } else if x > j && y > j {
                    // Both after insertion point - these are the shifted elements
                    // They maintain their relative order from before shifting
                }
            }
        }
        
        i = i + 1;
    }
}

}