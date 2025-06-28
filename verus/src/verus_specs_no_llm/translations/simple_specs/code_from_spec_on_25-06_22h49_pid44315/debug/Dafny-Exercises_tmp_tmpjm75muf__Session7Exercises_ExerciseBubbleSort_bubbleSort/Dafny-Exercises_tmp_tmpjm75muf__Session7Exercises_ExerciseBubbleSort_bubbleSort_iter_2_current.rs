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
    while i < f - 1
        invariant 
            c <= i <= f - 1,
            a.len() == old(a).len(),
            forall|j: int| 0 <= j < c ==> a[j as usize] == old(a)[j as usize],
            forall|j: int| f <= j < a.len() ==> a[j as usize] == old(a)[j as usize],
            multiset(a@.subrange(c as int, f as int)) == multiset(old(a)@.subrange(c as int, f as int)),
            sorted_seg(a, c as int, (i + 1) as int),
            forall|j: int, k: int| c <= j <= i && (i + 1) <= k < f ==> a[j as usize] <= a[k as usize]
    {
        let mut j = f - 1;
        while j > i + 1
            invariant 
                i + 1 < j <= f - 1,
                c <= i <= f - 1,
                a.len() == old(a).len(),
                forall|k: int| 0 <= k < c ==> a[k as usize] == old(a)[k as usize],
                forall|k: int| f <= k < a.len() ==> a[k as usize] == old(a)[k as usize],
                multiset(a@.subrange(c as int, f as int)) == multiset(old(a)@.subrange(c as int, f as int)),
                sorted_seg(a, c as int, (i + 1) as int),
                forall|k: int, l: int| c <= k <= i && (i + 1) <= l < f ==> a[k as usize] <= a[l as usize],
                forall|k: int| (i + 1) <= k < j ==> a[k as usize] <= a[j as usize]
        {
            if a[j - 1] > a[j] {
                let temp = a[j - 1];
                a.set(j - 1, a[j]);
                a.set(j, temp);
                
                // Proof that swap preserves multiset
                assert(multiset(a@.subrange(c as int, f as int)) == multiset(old(a)@.subrange(c as int, f as int)));
            }
            j = j - 1;
        }
        
        // After inner loop, prove that position i+1 has the correct element
        assert(forall|k: int| (i + 1) < k < f ==> a[(i + 1) as usize] <= a[k as usize]);
        assert(sorted_seg(a, c as int, (i + 2) as int));
        
        i = i + 1;
    }
    
    // Final assertion to help prove the postcondition
    assert(sorted_seg(a, c as int, f as int));
    true
}

}