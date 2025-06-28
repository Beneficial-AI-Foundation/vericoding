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
        
        // Store the original array for multiset reasoning
        proof {
            assert(a@.to_multiset() == old(a)@.to_multiset());
        }
        
        // Find the correct position for key by shifting elements
        while j > 0 && a[j - 1] > key
            invariant
                j <= i < a.len(),
                // The key value is preserved
                key == old(a)@[i as int],
                // Elements from j to i are all > key (shifted elements)
                forall|k: int| (j as int) <= k < (i as int) ==> a[k as nat] > key,
                // Elements from 0 to j-1 are sorted (if j > 0)
                j == 0 || isSorted(a, 0, j),
                // Elements from i+1 to end are unchanged
                forall|k: int| (i as int) < k < a.len() ==> a[k as nat] == old(a)@[k],
                // Elements from 0 to j-1 are unchanged from the start of this iteration
                forall|k: int| 0 <= k < (j as int) ==> a[k as nat] == old(a)@[k],
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
                if y < j {
                    // Both x and y are before the insertion point - they're unchanged and were sorted
                    assert(isSorted(old(a)@, 0, i));
                    assert(a[x as nat] == old(a)@[x]);
                    assert(a[y as nat] == old(a)@[y]);
                } else if x < j && y == j {
                    // x is before insertion point, y is the inserted key
                    // We know that when the inner loop exited, either j == 0 or a[j-1] <= key
                    if j > 0 {
                        assert(!(a[(j-1) as nat] > key)); // Loop condition was false
                        assert(x < j);
                        assert(a[x as nat] == old(a)@[x]);
                        // From the sorted property of the original prefix and the fact that
                        // we stopped shifting, we know a[x] <= key
                        if x == j - 1 {
                            assert(a[x as nat] <= key);
                        } else {
                            // x < j-1, so from transitivity of the sorted property:
                            assert(isSorted(old(a)@, 0, i));
                            assert(a[x as nat] <= a[(j-1) as nat]);
                            assert(a[(j-1) as nat] <= key);
                        }
                    }
                } else if x < j && y > j {
                    // x is before insertion, y is after (shifted element)
                    assert(a[y as nat] > key);
                    // Similar reasoning as above case for a[x] <= key
                    if j > 0 {
                        if x == j - 1 {
                            assert(a[x as nat] <= key);
                        } else {
                            assert(a[x as nat] <= a[(j-1) as nat]);
                            assert(a[(j-1) as nat] <= key);
                        }
                    } else {
                        // j == 0, so x < 0 which is impossible
                        assert(false);
                    }
                } else if x == j && y > j {
                    // x is the inserted key, y is a shifted element
                    assert(a[x as nat] == key);
                    assert(a[y as nat] > key);
                } else if x > j && y > j {
                    // Both are in the shifted region
                    // They maintain their relative order from before shifting
                    assert(a[x as nat] > key);
                    assert(a[y as nat] > key);
                    // The relative order is preserved during shifting
                    assert(old(a)@[x] == old(a)@[y-1] || (x < i && y <= i && old(a)@[x] <= old(a)@[y-1]));
                }
            }
        }
        
        // Prove multiset preservation
        assert(a@.to_multiset() == old(a)@.to_multiset()) by {
            // The multiset is preserved because we only moved elements around
            // and inserted the same key that was at position i
        }
        
        i = i + 1;
    }
}

}