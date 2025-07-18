use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: &[int], i: int, j: int) -> bool
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

pub fn bubbleSorta(a: &mut [int], c: usize, f: usize)
    requires 
        c <= f <= old(a).len(),
    ensures
        sorted_seg(a, c as int, f as int),
        a.subrange(c as int, f as int).to_multiset() == old(a).subrange(c as int, f as int).to_multiset(),
        a.subrange(0, c as int) == old(a).subrange(0, c as int) && a.subrange(f as int, old(a).len() as int) == old(a).subrange(f as int, old(a).len() as int),
{
}

}