use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
    if a.len() <= 1 {
        return true;
    }
    let first = a[0];
    let mut i = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|i: int, j: int| 0 <= i < j < a.len() && #[trigger] a@[i] == a@[j] ==> a@[j] == first,
            forall|k: int| 0 <= k < i ==> #[trigger] a@[k] == first
        decreases a.len() - i
    {
        if a[i] != first {
            return false;
        }
        i += 1;
    }
    return true;
}
// </vc-code>
// </vc-code>

fn main() {}
}