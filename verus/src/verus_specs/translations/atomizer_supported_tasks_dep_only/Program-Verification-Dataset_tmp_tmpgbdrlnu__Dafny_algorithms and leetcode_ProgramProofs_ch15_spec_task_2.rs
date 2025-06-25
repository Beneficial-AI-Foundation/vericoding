use vstd::prelude::*;

verus! {

spec fn SplitPoint(a: &[int], n: int) -> bool {
    forall|i: int, j: int| 0 <= i < n <= j < a.len() ==> a[i] <= a[j]
}

pub fn QuickSort(a: &mut [int])
    ensures
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@ == old(a)@.to_multiset(),
{
}

spec fn SwapFrame(a: &[int], old_a: &[int], lo: int, hi: int) -> bool
    recommends 
        0 <= lo <= hi <= a.len()
{
    (forall|i: int| (0 <= i < lo || hi <= i < a.len()) ==> a[i] == old_a[i]) && 
    a@.to_multiset() == old_a@.to_multiset()
}

pub fn QuickSortAux(a: &mut [int], lo: int, hi: int)
    requires
        0 <= lo <= hi <= a.len(),
        SplitPoint(a, lo) && SplitPoint(a, hi),
    ensures
        forall|i: int, j: int| lo <= i < j < hi ==> a[i] <= a[j],
        SwapFrame(a, old(a), lo, hi),
        SplitPoint(a, lo) && SplitPoint(a, hi),
{
}

pub fn Partition(a: &mut [int], lo: int, hi: int) -> (p: int)
    requires
        0 <= lo < hi <= a.len(),
        SplitPoint(a, lo) && SplitPoint(a, hi),
    ensures
        lo <= p < hi,
        forall|i: int| lo <= i < p ==> a[i] < a[p],
        forall|i: int| p <= i < hi ==> a[p] <= a[i],
        SplitPoint(a, lo) && SplitPoint(a, hi),
        SwapFrame(a, old(a), lo, hi),
{
}

}