use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn replace(a: &mut Vec<i32>, x: i32, y: i32)
    // post-conditions-start
    ensures
        a.len() == old(a).len(),
        forall|k: int| 0 <= k < old(a).len() && old(a)[k] == x ==> a[k] == y,
        forall|k: int| 0 <= k < old(a).len() && old(a)[k] != x ==> a[k] == old(a)[k],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let len = a.len();
    let old_a = *a;
    for i: usize in 0..len
        invariant
            i <= len,
            forall|j: int| 0 <= j < i ==> a@[j as int] == if old_a@[j] == x { y } else { old_a@[j] },
            forall|j: int| i as int <= j < len ==> a@[j] == old_a@[j],
    {
        if old_a@[i as int] == x {
            *a = a.update(i as int, y);
        }
    }
    // impl-end
}
// </vc-code>

fn main() {}
}