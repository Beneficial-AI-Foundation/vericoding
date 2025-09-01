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
    let tracked old_a: Seq<i32> = a@;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == old_a.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] if old_a[k] == x { a[k] == y } else { a[k] == old_a[k] },
            forall|k: int| i <= k < old_a.len() ==> #[trigger] a[k] == old_a[k],
    {
        if *a.index(i) == x {
            *a.index_mut(i) = y;
        }
        i += 1;
    }
}
// </vc-code>

fn main() {}
}