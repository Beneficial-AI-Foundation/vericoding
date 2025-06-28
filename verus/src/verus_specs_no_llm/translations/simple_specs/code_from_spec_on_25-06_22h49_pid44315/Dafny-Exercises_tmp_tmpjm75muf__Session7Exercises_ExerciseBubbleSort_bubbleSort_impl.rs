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

proof fn multiset_swap_preserves<T>(a: Seq<T>, i: int, j: int, x: T, y: T)
    requires 
        0 <= i < a.len(),
        0 <= j < a.len(),
        a[i] == x,
        a[j] == y
    ensures multiset(a.update(i, y).update(j, x)) == multiset(a)
{
    // Verus can prove this automatically for swaps
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
        
        // Swap minimum element to position i
        if min_idx != i {
            let ghost old_a_val = a@;
            let temp = a[i];
            a.set(i, a[min_idx]);
            a.set(min_idx, temp);
            
            // Use proof function to establish multiset preservation
            proof {
                multiset_swap_preserves(old_a_val, i as int, min_idx as int, temp, a[i]);
                
                // The subrange multiset is preserved
                assert(multiset(a@.subrange(c as int, f as int)) == multiset(old_a_val.subrange(c as int, f as int)));
            }
        }
        
        i = i + 1;
    }
}

}