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
    let mut idx: usize = 0;
    let mut res: usize = 0;
    let mut found: bool = false;
    while idx < n
        invariant idx <= n,
        invariant found == (exists |j: int| 0 <= j && j < idx as int && a[j as usize] == elem),
        invariant (found ==> (res < idx && a[res] == elem && (forall |j: int| 0 <= j && j < idx as int ==> (a[j as usize] == elem ==> j <= res as int)))),
    {
        if a[idx] == elem {
            res = idx;
            found = true;
        }
        idx = idx + 1;
    }
    res
}
// </vc-code>

fn main() {}
}