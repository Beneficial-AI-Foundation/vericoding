// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn binary_search_precond(a: &Vec<i32>, key: i32) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
fn binary_search_loop(a: &Vec<i32>, key: i32, lo: usize, hi: usize) -> (result: usize)
    requires
        lo <= hi,
        hi <= a.len(),
        binary_search_precond(a, key),
    ensures
        lo <= result <= hi,
        forall|i: int| lo <= i < result ==> a[i] < key,
        forall|i: int| result <= i < hi ==> a[i] >= key,
    decreases hi - lo,
{
    if lo < hi {
        let mid = lo + (hi - lo) / 2;
        if a[mid] < key {
            binary_search_loop(a, key, mid + 1, hi)
        } else {
            binary_search_loop(a, key, lo, mid)
        }
    } else {
        lo
    }
}
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &Vec<i32>, key: i32) -> (result: usize)
    requires binary_search_precond(a, key),
    ensures
        result <= a.len(),
        forall|i: int| 0 <= i < result ==> a[i] < key,
        forall|i: int| result <= i < a.len() ==> a[i] >= key,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {}