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

// Helper spec function to express multiset preservation more clearly
spec fn multiset_equivalent(a: &Vec<int>, b: &Vec<int>, start: int, end: int) -> bool
    requires 0 <= start <= end <= a.len() == b.len()
{
    &&& (forall|i: int| start <= i < end ==> exists|j: int| start <= j < end && a[i as usize] == b[j as usize])
    &&& (forall|i: int| start <= i < end ==> exists|j: int| start <= j < end && b[i as usize] == a[j as usize])
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
            // Sorted property for elements before i
            sorted_seg(a, c as int, i as int),
            // Elements before i are <= elements from i onwards (partial ordering)
            forall|k1: int, k2: int| c <= k1 < i && i <= k2 < f ==> a[k1 as usize] <= a[k2 as usize],
            // Elements outside the range are unchanged
            forall|k: int| 0 <= k < c ==> a[k as usize] == old(a)[k as usize],
            forall|k: int| f <= k < a.len() ==> a[k as usize] == old(a)[k as usize],
            // Multiset preservation within the working range
            forall|k: int| c <= k < f ==> exists|j: int| c <= j < f && a[k as usize] == old(a)[j as usize],
            forall|k: int| c <= k < f ==> exists|j: int| c <= j < f && old(a)[k as usize] == a[j as usize],
        decreases f - i
    {
        if i + 1 >= f {
            i = i + 1;
            continue;
        }
        
        // Find minimum element in range [i, f) and move it to position i
        let mut min_idx = i;
        let mut j = i + 1;
        
        // Find the minimum element in the remaining unsorted portion
        while j < f
            invariant
                c <= i < j <= f,
                i <= min_idx < j,
                f <= a.len(),
                a.len() == old(a).len(),
                sorted_seg(a, c as int, i as int),
                forall|k1: int, k2: int| c <= k1 < i && i <= k2 < f ==> a[k1 as usize] <= a[k2 as usize],
                forall|k: int| 0 <= k < c ==> a[k as usize] == old(a)[k as usize],
                forall|k: int| f <= k < a.len() ==> a[k as usize] == old(a)[k as usize],
                forall|k: int| c <= k < f ==> exists|l: int| c <= l < f && a[k as usize] == old(a)[l as usize],
                forall|k: int| c <= k < f ==> exists|l: int| c <= l < f && old(a)[k as usize] == a[l as usize],
                // min_idx points to minimum element in range [i, j)
                forall|k: int| i <= k < j ==> a[min_idx as usize] <= a[k as usize],
            decreases f - j
        {
            if a[j as usize] < a[min_idx as usize] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        // Swap elements at positions i and min_idx if they're different
        if min_idx != i {
            let temp = a[i as usize];
            a.set(i as usize, a[min_idx as usize]);
            a.set(min_idx as usize, temp);
            
            // Prove multiset preservation after swap
            assert(forall|k: int| c <= k < f && k != i && k != min_idx ==> 
                exists|l: int| c <= l < f && a[k as usize] == old(a)[l as usize]);
            assert(exists|l: int| c <= l < f && a[i as usize] == old(a)[l as usize]);
            assert(exists|l: int| c <= l < f && a[min_idx as usize] == old(a)[l as usize]);
        }
        
        // After placing minimum at position i, prove the ordering invariant
        assert(forall|k: int| (i + 1) <= k < f ==> a[i as usize] <= a[k as usize]);
        
        // Prove sorted segment extends
        if i > c {
            assert(a[(i - 1) as usize] <= a[i as usize]);
        }
        
        i = i + 1;
    }
    
    // Final proof obligations
    assert(i == f);
    assert(sorted_seg(a, c as int, f as int));
}

}