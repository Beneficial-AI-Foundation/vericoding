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
        
        while j > 0 && a[j - 1] > key
            invariant
                j <= i,
                i < a.len(),
                key == a[i],
                isSorted(a, 0, j),
                isSorted(a, j + 1, i + 1),
                forall|k: int| 0 <= k < j ==> a[k as nat] <= key,
                forall|k: int| j < k <= i ==> a[k as nat] >= key,
                a@.to_multiset() == old(a)@.to_multiset(),
        {
            a[j] = a[j - 1];
            j = j - 1;
        }
        
        a[j] = key;
        
        assert(isSorted(a, 0, i + 1));
        i = i + 1;
    }
}

}