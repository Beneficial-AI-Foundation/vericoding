use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
    // pre-conditions-start
    requires
        0 < a.len() < 100_000,
        exists|i: int| 0 <= i < a.len() && a[i] == elem,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= result < a.len(),
        forall|i: int| result < i < a.len() ==> a[i] != elem,
        a[result as int] == elem,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n: usize = a.len();
    let mut idx: usize = n;
    while idx > 0
        invariant idx <= n,
        invariant (forall |j: int| idx as int <= j && j < n as int ==> a[j as usize] != elem),
    {
        idx = idx - 1;
        if a[idx] == elem {
            return idx;
        }
    }
    proof {
        // loop terminated with idx == 0
        assert(idx == 0);
        // by invariant, no element in [0, n) equals elem
        assert(forall |j: int| 0 <= j && j < n as int ==> a[j as usize] != elem);
        // contradicts precondition that some element equals elem
        assert(!(exists |i: int| 0 <= i && i < n as int && a[i as usize] == elem));
        assert(exists |i: int| 0 <= i && i < n as int && a[i as usize] == elem);
        assert(false);
    }
    0
}
// </vc-code>

fn main() {}
}