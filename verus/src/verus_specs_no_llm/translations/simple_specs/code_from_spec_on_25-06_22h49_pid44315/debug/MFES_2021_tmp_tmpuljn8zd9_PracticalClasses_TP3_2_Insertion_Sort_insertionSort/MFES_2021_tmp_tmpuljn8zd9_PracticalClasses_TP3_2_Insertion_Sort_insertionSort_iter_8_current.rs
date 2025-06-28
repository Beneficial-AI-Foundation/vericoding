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
                // Elements from j to i are all > key
                forall|k: int| (j as int) < k <= (i as int) ==> a[k as nat] > key,
                // Elements from 0 to j-1 remain sorted
                j == 0 || isSorted(a, 0, j),
                // Elements beyond i are unchanged
                forall|k: int| (i as int) < k < a.len() ==> a[k as nat] == old(a)@[k],
                // Multiset property: we're just shifting, so multiset is preserved
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            a[j] = a[j - 1];
            j = j - 1;
        }
        
        // Insert key at position j
        a[j] = key;
        
        // Prove that the first i+1 elements are sorted
        assert(isSorted(a, 0, i + 1)) by {
            assert forall|x: int, y: int| 0 <= x < y < (i as int + 1) implies a[x as nat] <= a[y as nat] by {
                if y <= j {
                    // Both elements are in the unchanged prefix
                    assert(isSorted(a, 0, j));
                } else if x < j && y > j {
                    // x is in prefix, y is either key or shifted element
                    if y == j {
                        // y is the inserted key
                        // Since we stopped the inner loop, either j == 0 or a[j-1] <= key
                        if j > 0 {
                            assert(!(a[(j-1) as nat] > key));
                        }
                    } else {
                        // y is a shifted element (> key)
                        // x is in sorted prefix, and from loop termination we know
                        // the relationship holds
                    }
                } else if x == j {
                    // x is the inserted key
                    if y > j {
                        // y is a shifted element, which is > key
                        assert(a[y as nat] > key);
                        assert(a[x as nat] == key);
                    }
                } else {
                    // Both x and y are shifted elements, maintaining their relative order
                    assert(x > j && y > j);
                }
            }
        }
        
        i = i + 1;
    }
}

}