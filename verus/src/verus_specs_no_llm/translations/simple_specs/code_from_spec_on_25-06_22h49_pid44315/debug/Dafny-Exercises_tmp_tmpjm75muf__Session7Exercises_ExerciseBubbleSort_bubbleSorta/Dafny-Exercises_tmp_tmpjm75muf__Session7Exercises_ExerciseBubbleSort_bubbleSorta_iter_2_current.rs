use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted_seg(a: &Vec<int>, i: int, j: int) -> bool
    requires 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l as usize] <= a[k as usize]
}

spec fn multiset_between(a: &Vec<int>, b: &Vec<int>, start: int, end: int) -> bool
    requires 0 <= start <= end <= a.len() == b.len()
{
    forall|i: int| start <= i < end ==> exists|j: int| start <= j < end && a[i as usize] == b[j as usize]
}

fn bubbleSorta(a: &mut Vec<int>, c: usize, f: usize)
    requires 
        c <= f,
        f <= old(a).len(),
    ensures 
        a.len() == old(a).len(),
        sorted_seg(a, c as int, f as int),
        // Multiset preservation for the sorted segment
        forall|i: int| c <= i < f ==> exists|j: int| c <= j < f && a[i as usize] == old(a)[j as usize],
        forall|i: int| c <= i < f ==> exists|j: int| c <= j < f && old(a)[i as usize] == a[j as usize],
        // Elements outside the range are unchanged
        forall|i: int| 0 <= i < c ==> a[i as usize] == old(a)[i as usize],
        forall|i: int| f <= i < a.len() ==> a[i as usize] == old(a)[i as usize],
{
    if c >= f {
        return;
    }
    
    let mut i = c;
    while i < f
        invariant
            c <= i <= f,
            f <= a.len(),
            a.len() == old(a).len(),
            // Elements before i are correctly positioned relative to elements at i and beyond
            forall|k1: int, k2: int| c <= k1 < i && i <= k2 < f ==> a[k1 as usize] <= a[k2 as usize],
            // Elements outside the range are unchanged
            forall|k: int| 0 <= k < c ==> a[k as usize] == old(a)[k as usize],
            forall|k: int| f <= k < a.len() ==> a[k as usize] == old(a)[k as usize],
            // Multiset preservation
            forall|k: int| c <= k < f ==> exists|j: int| c <= j < f && a[k as usize] == old(a)[j as usize],
            forall|k: int| c <= k < f ==> exists|j: int| c <= j < f && old(a)[k as usize] == a[j as usize],
    {
        if i + 1 >= f {
            i = i + 1;
            continue;
        }
        
        let mut j = f - 1;
        while j > i
            invariant
                c <= i < j < f,
                f <= a.len(),
                a.len() == old(a).len(),
                // Elements before i are correctly positioned
                forall|k1: int, k2: int| c <= k1 < i && i <= k2 < f ==> a[k1 as usize] <= a[k2 as usize],
                // Elements outside the range are unchanged
                forall|k: int| 0 <= k < c ==> a[k as usize] == old(a)[k as usize],
                forall|k: int| f <= k < a.len() ==> a[k as usize] == old(a)[k as usize],
                // Multiset preservation
                forall|k: int| c <= k < f ==> exists|l: int| c <= l < f && a[k as usize] == old(a)[l as usize],
                forall|k: int| c <= k < f ==> exists|l: int| c <= l < f && old(a)[k as usize] == a[l as usize],
                // The minimum element in range [i, j] is at or before position i
                forall|k: int| i < k <= j ==> a[i as usize] <= a[k as usize],
        {
            if a[j - 1] > a[j] {
                // Swap elements
                let temp = a[j - 1];
                a.set(j - 1, a[j]);
                a.set(j, temp);
                
                // Proof that multiset is preserved after swap
                assert(forall|k: int| c <= k < f ==> exists|l: int| c <= l < f && a[k as usize] == old(a)[l as usize]);
                assert(forall|k: int| c <= k < f ==> exists|l: int| c <= l < f && old(a)[k as usize] == a[l as usize]);
            }
            j = j - 1;
        }
        
        // After inner loop, a[i] contains the minimum element from range [i, f)
        assert(forall|k: int| i < k < f ==> a[i as usize] <= a[k as usize]);
        
        i = i + 1;
    }
    
    // Prove that the final result is sorted
    assert(forall|k1: int, k2: int| c <= k1 <= k2 < f ==> a[k1 as usize] <= a[k2 as usize]);
}

}