use vstd::prelude::*;

verus! {

// <vc-helpers>
// (No helpers needed)
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
    let orig: Seq<i32> = a@;
    let n: int = a.len() as int;
    let mut i: int = 0;
    while i < n
        invariant { 0 <= i && i <= n };
        invariant { a.len() as int == n };
        invariant { forall |k: int| 0 <= k && k < i ==>
            (if orig@[k] == x { a[k as usize] == y } else { a[k as usize] == orig@[k] }) };
    {
        let idx: usize = i as usize;
        if a[idx] == x {
            a[idx] = y;
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}
}