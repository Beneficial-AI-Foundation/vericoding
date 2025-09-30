use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    let last = a.len() - 1;
    let first_val = a[0];
    let last_val = a[last];
    a[0] = last_val;
    a[last] = first_val;
}
// </vc-code>

fn main() {}

}