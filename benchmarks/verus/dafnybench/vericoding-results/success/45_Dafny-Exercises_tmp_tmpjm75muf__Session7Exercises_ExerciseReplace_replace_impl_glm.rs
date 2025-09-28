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
    let ghost old_v = v@;
    let old_len = v.len();

    for i in 0..old_len
        invariant
            v.len() == old_len,
            forall|k: int| 0 <= k < i ==> #[trigger] v@[k] == (if old_v[k] == x { y } else { old_v[k] }),
            forall|k: int| i <= k < old_len ==> #[trigger] v@[k] == old_v[k],
    {
        if v[i] == x {
            v[i] = y;
        }
    }
}
// </vc-code>

fn main() {
}

}