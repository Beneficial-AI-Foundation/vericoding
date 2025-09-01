use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
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
fn last_position(a: &[i32], elem: i32) -> (result: usize)
{
    let mut i: int = (a.len() as int) - 1;
    while i >= 0
    {
        if a[i] == elem {
            return i as usize;
        }
        i -= 1;
    }
    // The pre-condition ensures at least one occurrence, so this is unreachable
    assert(false);  // For safety, but pre-condition guarantees return above
    0
}
// </vc-code>

fn main() {}
}