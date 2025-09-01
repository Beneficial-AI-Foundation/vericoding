use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::view::*;
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let a_view = a.view();
    if a_view.len() == 0 {
        return true;
    }
    if a_view.len() == 1 {
        return true;
    }
    let first = a_view[0];
    let mut i = 1;
    while i < a_view.len()
        invariant
            1 <= i,
            forall|k: int| 0 <= k < i ==> a_view[k] == first
    {
        if a_view[i] != first {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

fn main() {}
}