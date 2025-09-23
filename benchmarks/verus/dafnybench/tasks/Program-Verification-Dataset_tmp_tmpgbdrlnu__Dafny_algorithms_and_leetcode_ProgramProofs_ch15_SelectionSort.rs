// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn split_point(a: &Vec<int>, n: int) -> bool {
    0 <= n <= a.len() &&
    forall|i: int, j: int| 0 <= i < n <= j < a.len() ==> a[i] <= a[j]
}

spec fn swap_frame(a_old: &Vec<int>, a_new: &Vec<int>, lo: int, hi: int) -> bool {
    0 <= lo <= hi <= a_old.len() &&
    a_old.len() == a_new.len() &&
    (forall|i: int| (0 <= i < lo || hi <= i < a_old.len()) ==> a_new[i] == a_old[i]) &&
    a_new@.to_multiset() == a_old@.to_multiset()
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<int>)
    ensures
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}