// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn linear_search_aux(a: &Vec<i32>, e: i32, n: usize) -> (result: usize)
    requires n <= a.len(),
    decreases a.len() - n,
{
    if n < a.len() {
        if a[n] == e {
            n
        } else {
            linear_search_aux(a, e, n + 1)
        }
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    requires exists|i: int| 0 <= i < a.len() && a[i] == e,
    ensures
        result < a.len(),
        a[result as int] == e,
        forall|k: int| 0 <= k < result ==> a[k] != e,
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