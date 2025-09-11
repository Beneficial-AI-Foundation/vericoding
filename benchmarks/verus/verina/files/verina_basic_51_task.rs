// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn binary_search_precond(a: &Vec<i32>, key: i32) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}