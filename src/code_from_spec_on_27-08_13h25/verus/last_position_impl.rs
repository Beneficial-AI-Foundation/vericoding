use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue is in the implementation logic
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
    let mut i: usize = a.len() - 1;
    let mut found = false;

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            !found ==> forall|j: int| i < j < a.len() ==> a[j] != elem,
            found ==> 0 <= i < a.len() && a[i as int] == elem && forall|j: int| i < j < a.len() ==> a[j] != elem,
            exists|k: int| 0 <= k < a.len() && a[k] == elem,
        decreases i
    {
        if a[i] == elem {
            found = true;
            break;
        }
        if i == 0 {
            break;
        }
        i = i - 1;
    }

    // Return the index i, which is guaranteed to be the last position due to the search order
    i
}
// </vc-code>

fn main() {}
}