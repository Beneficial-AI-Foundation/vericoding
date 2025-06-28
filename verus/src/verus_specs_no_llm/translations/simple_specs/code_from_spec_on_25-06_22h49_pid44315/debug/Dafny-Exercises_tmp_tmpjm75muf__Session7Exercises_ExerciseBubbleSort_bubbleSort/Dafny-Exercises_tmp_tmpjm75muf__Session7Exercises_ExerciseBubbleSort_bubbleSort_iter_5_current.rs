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
                forall|k: int| i <= k < j ==> a[min_idx as usize] <= a[k as usize]
        {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        // Swap minimum element to position i
        if min_idx != i {
            let temp = a[i];
            a.set(i, a[min_idx]);
            a.set(min_idx, temp);
        }
        
        // Prove that the sorted segment can be extended
        assert(forall|k: int| (i + 1) <= k < f ==> a[i as usize] <= a[k as usize]);
        
        // Prove sorted_seg extension
        assert(forall|l: int, k: int| c <= l < k < i ==> a[l as usize] <= a[k as usize]) by {
            assert(sorted_seg(a, c as int, i as int));
        }
        
        assert(forall|l: int, k: int| c <= l < k <= i ==> a[l as usize] <= a[k as usize]) by {
            if c <= l < k <= i {
                if k < i {
                    assert(a[l as usize] <= a[k as usize]);
                } else {
                    // k == i, need to show a[l] <= a[i]  
                    if l < i {
                        assert(a[l as usize] <= a[i as usize]);
                    }
                }
            }
        }
        
        i = i + 1;
    }
    
    true
}

}