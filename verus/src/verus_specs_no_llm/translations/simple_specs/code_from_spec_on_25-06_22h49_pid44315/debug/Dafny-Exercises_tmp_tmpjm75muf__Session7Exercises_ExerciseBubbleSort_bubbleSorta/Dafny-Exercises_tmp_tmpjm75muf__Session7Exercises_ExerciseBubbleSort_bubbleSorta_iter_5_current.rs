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
            // Sorted property for elements before i
            sorted_seg(a, c as int, i as int),
            // Elements before i are <= elements from i onwards
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
        
        let mut j = f - 1;
        while j > i
            invariant
                c <= i < j < f,
                f <= a.len(),
                a.len() == old(a).len(),
                // Previously sorted part remains sorted
                sorted_seg(a, c as int, i as int),
                // Elements before i are <= elements from i onwards
                forall|k1: int, k2: int| c <= k1 < i && i <= k2 < f ==> a[k1 as usize] <= a[k2 as usize],
                // Elements outside the range are unchanged from original
                forall|k: int| 0 <= k < c ==> a[k as usize] == old(a)[k as usize],
                forall|k: int| f <= k < a.len() ==> a[k as usize] == old(a)[k as usize],
                // Multiset preservation within working range
                forall|k: int| c <= k < f ==> exists|l: int| c <= l < f && a[k as usize] == old(a)[l as usize],
                forall|k: int| c <= k < f ==> exists|l: int| c <= l < f && old(a)[k as usize] == a[l as usize],
                // Current minimum is bubbled to position i
                forall|k: int| i < k <= j ==> a[i as usize] <= a[k as usize],
            decreases j - i
        {
            assert(j > 0);
            assert(j > i);
            assert(j < f);
            assert(f <= a.len());
            assert(j - 1 >= i);
            assert(j - 1 < a.len());
            assert(j < a.len());
            
            if a[(j - 1) as usize] > a[j as usize] {
                // Store old values for proof
                let old_j_minus_1 = a[(j - 1) as usize];
                let old_j = a[j as usize];
                
                // Swap elements j-1 and j
                a.set((j - 1) as usize, old_j);
                a.set(j as usize, old_j_minus_1);
                
                assert(a[(j - 1) as usize] == old_j);
                assert(a[j as usize] == old_j_minus_1);
                
                // Prove multiset is preserved after swap
                assert(forall|k: int| c <= k < f && k != (j - 1) && k != j ==> 
                    a[k as usize] == old(a)[k as usize]);
                
                // The swapped elements maintain multiset property
                assert(exists|l: int| c <= l < f && old_j_minus_1 == old(a)[l as usize]);
                assert(exists|l: int| c <= l < f && old_j == old(a)[l as usize]);
                
                // Prove ordering property is maintained
                assert(a[i as usize] <= a[(j - 1) as usize]);
                assert(forall|k: int| i < k < j ==> a[i as usize] <= a[k as usize]);
            }
            j = j - 1;
        }
        
        // After inner loop, minimum element from [i, f) is now at position i
        assert(forall|k: int| i < k < f ==> a[i as usize] <= a[k as usize]);
        
        // Prove that sorted segment extends by one
        if i > c {
            assert(sorted_seg(a, c as int, i as int));
            assert(a[(i - 1) as usize] <= a[i as usize]);
        }
        assert(sorted_seg(a, c as int, (i + 1) as int));
        
        i = i + 1;
    }
    
    // Final assertions to help with postcondition
    assert(sorted_seg(a, c as int, f as int));
    assert(forall|k: int| c <= k < f ==> exists|l: int| c <= l < f && a[k as usize] == old(a)[l as usize]);
    assert(forall|k: int| c <= k < f ==> exists|l: int| c <= l < f && old(a)[k as usize] == a[l as usize]);
}

}