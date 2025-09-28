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
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            old(v)@.len() == v@.len(),
            forall|k: int| #![trigger old(v)[k]] #![trigger v@[k]] 0 <= k < i ==> (old(v)[k] == x ==> v@[k] == y),
            forall|k: int| #![trigger old(v)[k]] #![trigger v@[k]] 0 <= k < i ==> (old(v)[k] != x ==> v@[k] == old(v)[k]),
            forall|k: int| #![trigger old(v)[k]] #![trigger v@[k]] i <= k < v.len() ==> v@[k] == old(v)[k]
        decreases v.len() - i
    {
        if v[i] == x {
            v[i] = y;
        }
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}