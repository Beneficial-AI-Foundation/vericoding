use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty helpers section - no updates needed
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
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == old(a).len(),
            forall|k: int| 0 <= k < i ==> #[trigger] if old(a)[k] == x { a[k] == y } else { a[k] == old(a)[k] },
            forall|k: int| i <= k < old(a).len() ==> #[trigger] a[k] == old(a)[k],
    {
        if a[i] == x {
            a[i] = y;
        }
        i += 1;
    }
}
// </vc-code>

fn main() {}
}