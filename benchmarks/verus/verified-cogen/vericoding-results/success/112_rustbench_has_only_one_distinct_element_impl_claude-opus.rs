// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    if a.len() == 0 {
        return true;
    }
    
    let first = a[0];
    let mut i = 1;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] == first,
        decreases a.len() - i,
    {
        if a[i] != first {
            assert(a[0] != a[i as int]);
            return false;
        }
        i += 1;
    }
    
    assert(forall|j: int| 0 <= j < a.len() ==> a[j] == first);
    assert(forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == first && a[j] == first);
    true
}
// </vc-code>

}
fn main() {}