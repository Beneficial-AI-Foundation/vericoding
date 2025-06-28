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
    let mut i = c;
    while i < f
        invariant
            c <= i <= f,
            f <= a.len(),
            a.len() == old(a).len(),
            // Elements before i are in their final sorted positions
            sorted_seg(a, c as int, i as int),
            // Elements outside the range are unchanged
            forall|k: int| 0 <= k < c ==> a[k as usize] == old(a)[k as usize],
            forall|k: int| f <= k < a.len() ==> a[k as usize] == old(a)[k as usize],
            // Multiset preservation
            forall|k: int| c <= k < f ==> exists|j: int| c <= j < f && a[k as usize] == old(a)[j as usize],
            forall|k: int| c <= k < f ==> exists|j: int| c <= j < f && old(a)[k as usize] == a[j as usize],
    {
        let mut j = f - 1;
        while j > i
            invariant
                c <= i < j < f,
                f <= a.len(),
                a.len() == old(a).len(),
                // Elements outside the range are unchanged
                forall|k: int| 0 <= k < c ==> a[k as usize] == old(a)[k as usize],
                forall|k: int| f <= k < a.len() ==> a[k as usize] == old(a)[k as usize],
                // Multiset preservation
                forall|k: int| c <= k < f ==> exists|l: int| c <= l < f && a[k as usize] == old(a)[l as usize],
                forall|k: int| c <= k < f ==> exists|l: int| c <= l < f && old(a)[k as usize] == a[l as usize],
        {
            if a[j - 1] > a[j] {
                // Swap elements
                let temp = a[j - 1];
                a.set(j - 1, a[j]);
                a.set(j, temp);
            }
            j = j - 1;
        }
        i = i + 1;
    }
}

}