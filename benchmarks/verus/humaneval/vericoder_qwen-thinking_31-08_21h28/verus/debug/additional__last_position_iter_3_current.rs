use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut i = a.len() - 1;
    while i >= 0 {
        invariant forall j: int :: (i as int) < j && j < (a.len() as int) ==> a[j as usize] != elem;
        if a[i] == elem {
            return i;
        }
        i = i - 1;
    }
}
// </vc-code>

fn main() {}
}