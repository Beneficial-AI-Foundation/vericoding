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

fn bubbleSort(a: &mut Vec<int>, c: usize, f: usize)
    requires 0 <= c <= f <= old(a).len()
    ensures a.len() == old(a).len()
    ensures sorted_seg(a, c as int, f as int)
    ensures forall|i: int| 0 <= i < c ==> a[i as usize] == old(a)[i as usize]
    ensures forall|i: int| f <= i < a.len() ==> a[i as usize] == old(a)[i as usize]
    ensures multiset(a@.subrange(c as int, f as int)) == multiset(old(a)@.subrange(c as int, f as int))
{
    if c >= f {
        return;
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
        decreases f - i
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
            decreases f - j
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
            let ghost old_a_before_swap = *a;
            let temp = a[i];
            a.set(i, a[min_idx]);
            a.set(min_idx, temp);
            
            // Prove multiset preservation after swap
            assert(multiset(a@.subrange(c as int, f as int)) == multiset(old_a_before_swap@.subrange(c as int, f as int)));
            
            // Prove that the swap maintains the cross-segment property
            assert(forall|p: int, q: int| c <= p < i && i <= q < f ==> a[p as usize] <= a[q as usize]);
            
            // Prove that sorted_seg is maintained for [c, i)
            assert(sorted_seg(a, c as int, i as int));
        }
        
        // Prove the invariants for the next iteration
        assert(forall|k: int| i < k < f ==> a[i as usize] <= a[k as usize]);
        
        // Prove sorted_seg extension
        assert(sorted_seg(a, c as int, (i + 1) as int));
        
        // Prove cross-segment property for next iteration
        assert(forall|p: int, q: int| c <= p < (i + 1) && (i + 1) <= q < f ==> a[p as usize] <= a[q as usize]);
        
        i = i + 1;
    }
}

}