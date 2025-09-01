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
    for i in (0..a.len()).rev()
        invariant
            forall j: int :: i < j < a.len() ==> a[j as usize] != elem,
            exists j: int :: 0 <= j <= i && a[j as usize] == elem
    {
        if a[i] == elem {
            return i;
        }
    }
    assert(false);
}
// </vc-code>

fn main() {}
}