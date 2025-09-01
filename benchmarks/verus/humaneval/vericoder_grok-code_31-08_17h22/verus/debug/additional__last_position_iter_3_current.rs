use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty HELPERS section
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
{
    let mut i: int = (a.len() as int) - 1;
    while i >= 0
        invariant
            i >= -1,
            i < a.len() as int,
            forall |j: int| #[trigger] i < j && j < a.len() && a@[j] != elem,
    {
        if a@[i as usize] == elem {
            return i as usize;
        }
        i -= 1;
    }
    unreachable!();
}
// </vc-code>

fn main() {}
}