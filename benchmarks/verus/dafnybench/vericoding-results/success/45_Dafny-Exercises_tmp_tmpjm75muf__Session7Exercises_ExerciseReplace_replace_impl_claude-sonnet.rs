use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn replace(v: &mut Vec<i32>, x: i32, y: i32)
    ensures
        forall|k: int| 0 <= k < old(v).len() && old(v)[k] == x ==> v[k] == y,
        forall|k: int| 0 <= k < old(v).len() && old(v)[k] != x ==> v[k] == old(v)[k],
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            v.len() == old(v).len(),
            forall|k: int| 0 <= k < i && old(v)[k] == x ==> v[k] == y,
            forall|k: int| 0 <= k < i && old(v)[k] != x ==> v[k] == old(v)[k],
            forall|k: int| i <= k < v.len() ==> v[k] == old(v)[k],
        decreases v.len() - i,
    {
        if v[i] == x {
            v.set(i, y);
        }
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}