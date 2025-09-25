// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn split_point(a: Seq<int>, n: int) -> bool {
    forall|i: int, j: int| 0 <= i < n <= j < a.len() ==> a[i] <= a[j]
}

spec fn swap_frame(a_old: Seq<int>, a_new: Seq<int>, lo: int, hi: int) -> bool
    recommends 0 <= lo <= hi <= a_old.len() && a_old.len() == a_new.len()
{
    (forall|i: int| (0 <= i < lo || hi <= i < a_new.len()) ==> a_new[i] == a_old[i]) 
    && a_new.to_multiset() =~= a_old.to_multiset()
}

fn partition(a: &mut Vec<int>, lo: usize, hi: usize) -> (p: usize)
    requires 
        0 <= lo < hi <= old(a).len(),
        split_point(old(a)@, lo as int) && split_point(old(a)@, hi as int),
    ensures
        lo <= p < hi,
        forall|i: int| lo <= i < p ==> a@[i] < a@[p as int],
        forall|i: int| p <= i < hi ==> a@[p as int] <= a@[i],
        split_point(a@, lo as int) && split_point(a@, hi as int),
        swap_frame(old(a)@, a@, lo as int, hi as int),
{
    assume(false);
    lo
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn quick_sort_aux(a: &mut Vec<int>, lo: usize, hi: usize)
    requires 
        0 <= lo <= hi <= old(a).len(),
        split_point(old(a)@, lo as int) && split_point(old(a)@, hi as int),
    ensures
        forall|i: int, j: int| lo <= i < j < hi ==> a@[i] <= a@[j],
        swap_frame(old(a)@, a@, lo as int, hi as int),
        split_point(a@, lo as int) && split_point(a@, hi as int),
    decreases hi - lo
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}