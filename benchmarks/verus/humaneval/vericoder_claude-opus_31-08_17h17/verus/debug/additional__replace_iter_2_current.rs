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
    let n = a.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            a.len() == n,
            n == old(a).len(),
            0 <= i <= n,
            forall|k: int| 0 <= k < i && old(a)[k] == x ==> a[k] == y,
            forall|k: int| 0 <= k < i && old(a)[k] != x ==> a[k] == old(a)[k],
            forall|k: int| i <= k < n ==> a[k] == old(a)[k],
        decreases n - i
    {
        if a[i] == x {
            a.set(i, y);
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}
}