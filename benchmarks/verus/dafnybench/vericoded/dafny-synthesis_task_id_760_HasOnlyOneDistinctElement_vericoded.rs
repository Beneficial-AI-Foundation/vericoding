use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    ensures 
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
// </vc-spec>
// <vc-code>
{
    if a.len() <= 1 {
        return true;
    }
    
    let first_element = a[0];
    
    for i in 1..a.len()
        invariant
            forall|k: int| 0 <= k < i ==> a[k] == first_element,
    {
        if a[i] != first_element {
            assert(a[0] != a[i as int]);
            assert(0 <= 0 < a.len() && 0 <= i < a.len() && a[0] != a[i as int]);
            return false;
        }
    }
    
    assert(forall|k: int| 0 <= k < a.len() ==> a[k] == first_element);
    assert(forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]);
    
    true
}
// </vc-code>

fn main() {}

}