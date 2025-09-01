use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    if a.len() == 0 {
        return true;
    }
    
    let first_element = a[0];
    let mut i = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] == first_element,
        decreases a.len() - i,
    {
        if a[i] != first_element {
            assert(a[0] != a[i as int]);
            return false;
        }
        i += 1;
    }
    
    assert(forall|k: int| 0 <= k < a.len() ==> a[k] == first_element);
    true
}
// </vc-code>

fn main() {}
}