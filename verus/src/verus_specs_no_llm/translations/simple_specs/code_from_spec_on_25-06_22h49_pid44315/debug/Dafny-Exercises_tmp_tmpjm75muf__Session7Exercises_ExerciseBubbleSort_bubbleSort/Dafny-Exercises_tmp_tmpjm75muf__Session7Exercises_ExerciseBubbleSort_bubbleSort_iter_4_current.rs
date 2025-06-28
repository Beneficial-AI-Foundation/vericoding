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
            sorted_seg(a, c as int, i as int)
    {
        let mut j = i + 1;
        while j < f
            invariant 
                i < j <= f,
                c <= i < f,
                a.len() == old(a).len(),
                forall|k: int| 0 <= k < c ==> a[k as usize] == old(a)[k as usize],
                forall|k: int| f <= k < a.len() ==> a[k as usize] == old(a)[k as usize],
                multiset(a@.subrange(c as int, f as int)) == multiset(old(a)@.subrange(c as int, f as int)),
                sorted_seg(a, c as int, i as int),
                forall|k: int| i < k < j ==> a[i as usize] <= a[k as usize]
        {
            if a[i] > a[j] {
                // Swap elements
                let temp = a[i];
                a.set(i, a[j]);
                a.set(j, temp);
            }
            
            // Maintain the property that a[i] <= a[k] for all k in [i+1, j]
            assert(a[i as usize] <= a[j as usize]);
            
            j = j + 1;
        }
        
        // After inner loop, a[i] is <= all elements in [i+1, f)
        // This means we can extend the sorted segment
        assert(forall|k: int| i < k < f ==> a[i as usize] <= a[k as usize]);
        assert(sorted_seg(a, c as int, i as int));
        assert(sorted_seg(a, c as int, (i + 1) as int));
        
        i = i + 1;
    }
    
    // At this point i == f, so we've sorted the entire segment
    assert(i == f);
    assert(sorted_seg(a, c as int, f as int));
    true
}

}