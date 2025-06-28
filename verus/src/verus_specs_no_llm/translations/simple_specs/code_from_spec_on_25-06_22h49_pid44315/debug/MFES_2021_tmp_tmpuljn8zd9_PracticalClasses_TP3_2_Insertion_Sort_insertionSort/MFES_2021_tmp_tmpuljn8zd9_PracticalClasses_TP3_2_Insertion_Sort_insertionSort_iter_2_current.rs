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
    let mut i: usize = 1;
    
    while i < a.len()
        invariant 
            i <= a.len(),
            isSorted(a, 0, i),
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        let key = a[i];
        let mut j = i;
        
        // Store the original multiset before the inner loop
        let ghost orig_multiset = a@.to_multiset();
        
        while j > 0 && a[j - 1] > key
            invariant
                j <= i,
                i < a.len(),
                key == old(a)[i],
                // The portion before j is sorted and all elements <= key
                isSorted(a, 0, j),
                forall|k: int| 0 <= k < j ==> a[k as nat] <= key,
                // The portion from j+1 to i+1 is sorted and all elements >= key
                j + 1 <= i + 1 ==> isSorted(a, j + 1, i + 1),
                forall|k: int| j + 1 <= k <= i ==> a[k as nat] >= key,
                // Elements at positions j through i are shifted versions of original elements
                forall|k: int| j < k <= i ==> a[k as nat] == old(a)[(k - 1) as nat],
                // Multiset is preserved (key temporarily duplicated)
                a@.to_multiset().remove(key) == orig_multiset.remove(key),
                a@.to_multiset().count(key) == orig_multiset.count(key) + 1,
        {
            a[j] = a[j - 1];
            j = j - 1;
        }
        
        a[j] = key;
        
        // Prove that inserting key at position j maintains sortedness
        assert(forall|k: int| 0 <= k < j ==> a[k as nat] <= key);
        assert(forall|k: int| j < k <= i ==> a[k as nat] >= key);
        assert(j < i + 1 ==> a[j] <= a[j + 1]);
        assert(j > 0 ==> a[j - 1] <= a[j]);
        assert(isSorted(a, 0, i + 1));
        
        i = i + 1;
    }
}

}