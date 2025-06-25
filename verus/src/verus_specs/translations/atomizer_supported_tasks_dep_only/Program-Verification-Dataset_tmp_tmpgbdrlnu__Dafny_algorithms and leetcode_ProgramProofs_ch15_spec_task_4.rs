use vstd::prelude::*;

verus! {

spec fn SplitPoint(a: &[int], n: int) -> bool {
    forall|i: int, j: int| 0 <= i < n <= j < a.len() ==> a[i] <= a[j]
}

spec fn SwapFrame(a: &[int], old_a: &[int], lo: int, hi: int) -> bool
    requires 0 <= lo <= hi <= a.len()
{
    (forall|i: int| (0 <= i < lo || hi <= i < a.len()) ==> a[i] == old_a[i]) && 
    a@ == old_a@
}

pub fn Partition(a: &mut [int], lo: int, hi: int) -> (p: int)
    requires 
        0 <= lo < hi <= old(a).len(),
        SplitPoint(&*old(a), lo) && SplitPoint(&*old(a), hi)
    ensures 
        lo <= p < hi,
        forall|i: int| lo <= i < p ==> a[i] < a[p],
        forall|i: int| p <= i < hi ==> a[p] <= a[i],
        SplitPoint(&*a, lo) && SplitPoint(&*a, hi),
        SwapFrame(&*a, &*old(a), lo, hi)
{
}

}