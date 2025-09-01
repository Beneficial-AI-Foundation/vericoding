use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::prelude::*;
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
            1 <= i && i < a.len(),
            forall|k: usize| k < i ==> a@[k] == first
    {
        if a[i] != first {
            return false;
        }
        i += 1;
    }
    list_elements_same(a@, first)
}
// </vc-code>

fn main() {}
}