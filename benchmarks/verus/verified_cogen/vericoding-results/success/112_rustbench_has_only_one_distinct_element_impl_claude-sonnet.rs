// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn all_elements_equal(a: &[i32]) -> bool {
    forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]
}

spec fn exists_different_elements(a: &[i32]) -> bool {
    exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j]
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    ensures
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clause to while loop */
    if a.len() <= 1 {
        return true;
    }
    
    let first_element = a[0];
    let mut i = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] == first_element,
        decreases a.len() - i
    {
        if a[i] != first_element {
            return false;
        }
        i += 1;
    }
    
    true
}
// </vc-code>

}
fn main() {}