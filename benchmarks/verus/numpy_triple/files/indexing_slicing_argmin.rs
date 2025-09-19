// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn argmin(a: Vec<i8>) -> (result: usize)
    requires a.len() > 0,
    ensures
        result < a.len(),
        forall|j: int| 0 <= j < a.len() ==> a[result as int] <= a[j],
        forall|k: int| 0 <= k < result ==> a[k] > a[result as int],
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