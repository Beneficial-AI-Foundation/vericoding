// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn swap_first_and_last(a: &mut Vec<i32>)
    requires
        old(a).len() > 0,
    ensures
        a.len() == old(a).len(),
        a[0] == old(a)[old(a).len() - 1],
        a[a.len() - 1] == old(a)[0],
        forall|k: int| 1 <= k < a.len() - 1 ==> a[k] == old(a)[k],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}