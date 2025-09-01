use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let len = a.len() as nat;
    for i in 0..len
        invariant
            i <= len as int,
            forall|j: int| 0 <= j < i ==> a@[j] == if old(a)@[j] == x { y } else { old(a)@[j] },
            forall|j: int| i <= j < len as int ==> a@[j] == old(a)@[j],
    {
        if old(a)@[i] == x {
            a[i as usize] = y;
        }
    }
}
// </vc-code>

fn main() {}
}