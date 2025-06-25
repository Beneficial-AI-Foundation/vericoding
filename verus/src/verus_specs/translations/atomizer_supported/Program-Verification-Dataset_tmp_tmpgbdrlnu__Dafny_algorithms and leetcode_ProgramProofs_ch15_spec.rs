use vstd::prelude::*;

verus! {

spec fn split_point(a: &[int], n: int) -> bool {
    forall|i: int, j: int| 0 <= i < n <= j < a.len() ==> a[i] <= a[j]
}

pub fn selection_sort(a: &mut [int])
    ensures forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
    ensures a@.to_multiset() == old(a)@.to_multiset(),
{
}

pub fn quick_sort(a: &mut [int])
    ensures forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
    ensures a@.to_multiset() == old(a)@.to_multiset(),
{
}

spec fn swap_frame(a: &[int], old_a: &[int], lo: int, hi: int) -> bool
    recommends 0 <= lo <= hi <= a.len()
{
    true
}

spec fn swap_frame_full(a: &[int], old_a: &[int], lo: int, hi: int) -> bool
    recommends 0 <= lo <= hi <= a.len()
{
    (forall|i: int| (0 <= i < lo || hi <= i < a.len()) ==> a[i] == old_a[i]) && 
    a@.to_multiset() == old_a@.to_multiset()
}

pub fn quick_sort_aux(a: &mut [int], lo: int, hi: int)
    requires 0 <= lo <= hi <= a.len(),
    requires split_point(a, lo) && split_point(a, hi),
    ensures forall|i: int, j: int| lo <= i < j < hi ==> a[i] <= a[j],
    ensures swap_frame_full(a, &old(a), lo, hi),
    ensures split_point(a, lo) && split_point(a, hi),
{
}

pub fn partition(a: &mut [int], lo: int, hi: int) -> (p: int)
    requires 0 <= lo < hi <= a.len(),
    requires split_point(a, lo) && split_point(a, hi),
    ensures lo <= p < hi,
    ensures forall|i: int| lo <= i < p ==> a[i] < a[p as int],
    ensures forall|i: int| p <= i < hi ==> a[p as int] <= a[i],
    ensures split_point(a, lo) && split_point(a, hi),
    ensures swap_frame_full(a, &old(a), lo, hi),
{
    0
}

}