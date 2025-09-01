use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helper code needed
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
    let len: usize = a.len();
    let len_ghost: int = len as int;
    let mut i: int = 0;
    while i < len_ghost
        invariant
            0 <= i <= len_ghost,
            a.len() as int == len_ghost,
            forall|j: int| #[trigger] 0 <= j < i ==> a@[j] == if old(a)@[j] == x { y } else { old(a)@[j] },
            forall|j: int| i <= j < len_ghost ==> a@[j] == old(a)@[j],
    {
        if a[i] == x {
            a[i] = y;
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}
}