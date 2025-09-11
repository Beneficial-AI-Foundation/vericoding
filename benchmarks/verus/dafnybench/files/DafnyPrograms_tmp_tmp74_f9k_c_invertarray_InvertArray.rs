// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn invert_array(a: &mut Vec<i32>)
    ensures
        a.len() == old(a).len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] == old(a)[a.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}