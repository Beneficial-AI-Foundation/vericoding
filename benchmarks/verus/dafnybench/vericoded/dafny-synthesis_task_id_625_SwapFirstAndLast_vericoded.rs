use vstd::prelude::*;

verus! {

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
        forall|k: int| 1 <= k < old(a).len() - 1 ==> a[k] == old(a)[k],
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    assert(n > 0);
    assert(n >= 1);
    assert(0 <= n - 1);
    assert(n - 1 < n);

    let first = a[0];
    let last = a[n - 1];
    a[0] = last;
    a[n - 1] = first;
}
// </vc-code>

fn main() {
}

}