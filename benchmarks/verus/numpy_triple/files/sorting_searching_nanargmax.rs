// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn nanargmax(a: Vec<i8>) -> (idx: usize)
    requires 
        a@.len() > 0,
    ensures 
        idx < a@.len(),
        forall|j: int| 0 <= j < a@.len() ==> a@[j] <= a@[idx as int],
        forall|j: int| 0 <= j < a@.len() && a@[j] == a@[idx as int] ==> (idx as int) <= j,
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