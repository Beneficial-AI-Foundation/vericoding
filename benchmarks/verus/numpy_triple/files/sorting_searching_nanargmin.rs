// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn nanargmin(a: Vec<i8>) -> (result: usize)
    requires 
        a.len() > 0,
    ensures
        result < a.len(),
        forall|j: int| 0 <= j < a@.len() ==> a[result as int] <= a[j],
        forall|j: int| 0 <= j < result ==> a[j] > a[result as int],
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}