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
    let n = a.len() as int;
    let mut i = n - 1;
    while i >= 0 {
        invariant forall j: int :: i < j && j < n ==> a[j as usize] != elem;
        if a[i as usize] == elem {
            return i as usize;
        }
        i = i - 1;
    }
}
// </vc-code>

fn main() {}
}