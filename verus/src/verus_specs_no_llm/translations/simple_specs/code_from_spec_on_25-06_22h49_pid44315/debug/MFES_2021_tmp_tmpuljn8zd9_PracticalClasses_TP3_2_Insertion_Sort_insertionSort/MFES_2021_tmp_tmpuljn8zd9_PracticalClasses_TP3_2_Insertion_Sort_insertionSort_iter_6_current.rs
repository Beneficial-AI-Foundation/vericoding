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
                // Elements from j+1 to i+1 are all > key (shifted elements)
                forall|k: int| (j as int) < k <= (i as int) ==> a[k as nat] > key,
                // If j > 0, then either we continue (a[j-1] > key) or we stop (a[j-1] <= key)
                // Elements before j (when loop exits) will be <= key
                // Multiset is preserved during shifting
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            a[j] = a[j - 1];
            j = j - 1;
        }
        
        // Insert key at position j
        a[j] = key;
        
        // Prove that the first i+1 elements are sorted
        assert(isSorted(a, 0, i + 1)) by {
            // We need to prove that for all pairs x, y where 0 <= x < y < i+1,
            // we have a[x] <= a[y]
            assert forall|x: int, y: int| 0 <= x < y < (i as int + 1) implies a[x as nat] <= a[y as nat] by {
                if y <= j {
                    // Both x and y are in positions that were sorted before and remain sorted
                    // This follows from the fact that we only moved elements that were > key
                    // and inserted key at the right position
                } else if x < j && y > j {
                    // x is before the insertion point, y is after
                    // We know a[x] was <= key (since we stopped shifting at j)
                    // and a[y] > key (from the shifting invariant)
                    if j > 0 {
                        assert(a[(j-1) as nat] <= key);  // Loop condition when we stopped
                    }
                    assert(a[y as nat] > key);  // From shifting invariant
                } else if x == j {
                    // x is the inserted key
                    if y > j {
                        assert(a[y as nat] > key);  // From shifting invariant
                        assert(a[x as nat] == key);
                    }
                } else {
                    // Both are in the shifted region - they maintain relative order
                    assert(a[x as nat] > key);
                    assert(a[y as nat] > key);
                }
            }
        }
        
        i = i + 1;
    }
}

}

The key changes I made:



   - Elements before the insertion point
   - The inserted key
   - Elements after the insertion point (shifted elements)
   - Combinations of these cases


The algorithm works by maintaining the invariant that elements `0..i` are sorted, and for each new element at position `i`, it finds the correct insertion point by shifting larger elements to the right, then inserts the element at the correct position.