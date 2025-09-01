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
    let mut i: nat = 0;
    while i < a.len() {
        invariant forall j: int :: 0 <= j && j < i ==> a@j == (if old(a)@j == x { y } else { old(a)@j })
        if a@i == x {
            a@i = y;
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}
}