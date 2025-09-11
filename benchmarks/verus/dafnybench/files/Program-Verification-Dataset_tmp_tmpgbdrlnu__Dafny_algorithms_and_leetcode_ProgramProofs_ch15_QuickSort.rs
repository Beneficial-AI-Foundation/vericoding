// <vc-preamble>
use vstd::prelude::*;

verus! {

fn partition(a: &mut Vec<int>, lo: usize, hi: usize) -> (p: usize)
    requires 0 <= lo < hi <= old(a).len(),
    ensures lo <= p < hi,
{
    assume(false);
    0
}

spec fn split_point(a: &Vec<int>, n: usize) -> bool
    recommends 0 <= n <= a.len(),
{
    forall|i: int, j: int| 0 <= i < n && n <= j < a.len() ==> a[i] <= a[j]
}

spec fn swap_frame(a: &Vec<int>, old_a: &Vec<int>, lo: usize, hi: usize) -> bool
    recommends 0 <= lo <= hi <= a.len(),
{
    (forall|i: int| (0 <= i < lo || hi <= i < a.len()) ==> a[i] == old_a[i]) &&
    a@.to_multiset() =~= old_a@.to_multiset()
}

fn quick_sort_aux(a: &mut Vec<int>, lo: usize, hi: usize)
    requires 
        0 <= lo <= hi <= old(a).len(),
        split_point(old(a), lo),
        split_point(old(a), hi),
    ensures 
        forall|i: int, j: int| lo <= i < j < hi ==> a[i] <= a[j],
        swap_frame(a, old(a), lo, hi),
        split_point(a, lo),
        split_point(a, hi),
    decreases hi - lo,
{
    assume(false);
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn quick_sort(a: &mut Vec<int>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() =~= old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}