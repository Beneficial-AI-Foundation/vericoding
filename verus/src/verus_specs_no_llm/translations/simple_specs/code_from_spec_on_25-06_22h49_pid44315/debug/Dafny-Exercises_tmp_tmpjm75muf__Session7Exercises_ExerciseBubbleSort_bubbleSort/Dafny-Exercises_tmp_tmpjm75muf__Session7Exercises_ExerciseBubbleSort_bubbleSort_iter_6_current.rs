use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted_seg(a: &[int], i: int, j: int) -> bool 
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l < k < j ==> a[l as usize] <= a[k as usize]
}

fn bubbleSort(a: &mut Vec<int>, c: usize, f: usize) -> (result: bool)
    requires 0 <= c <= f <= old(a).len()
    ensures a.len() == old(a).len()
    ensures sorted_seg(a, c as int, f as int)
    ensures forall|i: int| 0 <= i < c ==> a[i as usize] == old(a)[i as usize]
    ensures forall|i: int| f <= i < a.len() ==> a[i as usize] == old(a)[i as usize]
    ensures multiset(a@.subrange(c as int, f as int)) == multiset(old(a)@.subrange(c as int, f as int))
{
    if c >= f {
        return true;
    }
    
    let mut i = c;
    while i < f
        invariant 
            c <= i <= f,
            a.len() == old(a).len(),
            forall|j: int| 0 <= j < c ==> a[j as usize] == old(a)[j as usize],
            forall|j: int| f <= j < a.len() ==> a[j as usize] == old(a)[j as usize],
            multiset(a@.subrange(c as int, f as int)) == multiset(old(a)@.subrange(c as int, f as int)),
            sorted_seg(a, c as int, i as int),
            forall|p: int, q: int| c <= p < i && i <= q < f ==> a[p as usize] <= a[q as usize]
    {
        // Find minimum element in range [i, f) and move it to position i
        let mut min_idx = i;
        let mut j = i + 1;
        
        // Find the minimum element in the remaining unsorted portion
        while j < f
            invariant 
                i <= min_idx < f,
                i < j <= f,
                c <= i < f,
                a.len() == old(a).len(),
                forall|k: int| 0 <= k < c ==> a[k as usize] == old(a)[k as usize],
                forall|k: int| f <= k < a.len() ==> a[k as usize] == old(a)[k as usize],
                multiset(a@.subrange(c as int, f as int)) == multiset(old(a)@.subrange(c as int, f as int)),
                sorted_seg(a, c as int, i as int),
                forall|p: int, q: int| c <= p < i && i <= q < f ==> a[p as usize] <= a[q as usize],
                forall|k: int| i <= k < j ==> a[min_idx as usize] <= a[k as usize]
        {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        // At this point, min_idx points to minimum element in [i, f)
        assert(forall|k: int| i <= k < f ==> a[min_idx as usize] <= a[k as usize]);
        
        // Swap minimum element to position i
        if min_idx != i {
            let temp = a[i];
            a.set(i, a[min_idx]);
            a.set(min_idx, temp);
        }
        
        // After swap, a[i] is the minimum of range [i, f)
        assert(forall|k: int| (i + 1) <= k < f ==> a[i as usize] <= a[k as usize]);
        
        // Prove that elements before i are still <= a[i] (which is now minimum of [i, f))
        assert(forall|p: int| c <= p < i ==> a[p as usize] <= a[i as usize]);
        
        // Prove sorted_seg extension: the segment [c, i+1) is now sorted
        assert(sorted_seg(a, c as int, (i + 1) as int)) by {
            assert(forall|l: int, k: int| c <= l < k < (i + 1) ==> a[l as usize] <= a[k as usize]) by {
                if c <= l < k < (i + 1) {
                    if k < i {
                        // Both l and k are in the already sorted portion [c, i)
                        assert(a[l as usize] <= a[k as usize]);
                    } else {
                        // k == i, l < i, so we need a[l] <= a[i]
                        assert(l < i);
                        assert(a[l as usize] <= a[i as usize]);
                    }
                }
            }
        }
        
        // Maintain the cross-segment property
        assert(forall|p: int, q: int| c <= p < (i + 1) && (i + 1) <= q < f ==> a[p as usize] <= a[q as usize]) by {
            if c <= p < (i + 1) && (i + 1) <= q < f {
                if p < i {
                    // p is in [c, i), q is in [i+1, f)
                    // We know a[p] <= a[i] and a[i] <= a[q], so a[p] <= a[q]
                    assert(a[p as usize] <= a[i as usize]);
                    assert(a[i as usize] <= a[q as usize]);
                    assert(a[p as usize] <= a[q as usize]);
                } else {
                    // p == i, q is in [i+1, f)
                    assert(a[i as usize] <= a[q as usize]);
                }
            }
        }
        
        i = i + 1;
    }
    
    true
}

}