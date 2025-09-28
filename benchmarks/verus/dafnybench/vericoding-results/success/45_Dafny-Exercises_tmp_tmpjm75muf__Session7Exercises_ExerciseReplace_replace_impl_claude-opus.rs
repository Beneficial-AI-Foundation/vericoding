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
    let n = v.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            n == v.len(),
            n == old(v).len(),
            // Elements before i have been processed correctly
            forall|k: int| 0 <= k < i && old(v)[k] == x ==> v[k] == y,
            forall|k: int| 0 <= k < i && old(v)[k] != x ==> v[k] == old(v)[k],
            // Elements from i onwards are unchanged
            forall|k: int| i <= k < n ==> v[k] == old(v)[k],
        decreases n - i,
    {
        if v[i] == x {
            v.set(i, y);
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}