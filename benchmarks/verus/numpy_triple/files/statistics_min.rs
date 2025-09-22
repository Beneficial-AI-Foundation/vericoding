// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures
        exists|i: int| 0 <= i < a@.len() && a@[i] == result as int,
        forall|i: int| 0 <= i < a@.len() ==> result as int <= a@[i],
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