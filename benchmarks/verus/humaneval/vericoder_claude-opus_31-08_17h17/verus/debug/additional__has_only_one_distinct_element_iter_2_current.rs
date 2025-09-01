use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
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
    
    let first = a[0];
    let mut i: usize = 1;
    
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
        i = i + 1;
    }
    
    assert(forall|j: int| 0 <= j < a.len() ==> a[j] == first);
    assert(forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]);
    true
}
// </vc-code>

fn main() {}
}