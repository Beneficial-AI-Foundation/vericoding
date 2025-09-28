use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    ensures 
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
// </vc-spec>
// <vc-code>
{
    if a.len() == 0 {
        // Empty array trivially satisfies the condition
        return true;
    }
    
    let first = a[0];
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            first == a[0],  // Add invariant that first equals a[0]
            forall|j: int| 0 <= j < i ==> a[j] == first,
        decreases
            a.len() - i,
    {
        if a[i] != first {
            // Found an element different from the first one
            assert(a[0] == first);  // Now this should verify
            assert(a[i as int] != first);
            assert(0 <= 0 < a.len() && 0 <= i < a.len() && a[0] != a[i as int]);
            return false;
        }
        i = i + 1;
    }
    
    // All elements equal to first
    assert(forall|j: int| 0 <= j < a.len() ==> a[j] == first);
    assert(forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]) by {
        assert forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() implies a[i] == a[j] by {
            assert(a[i] == first);
            assert(a[j] == first);
        }
    }
    true
}
// </vc-code>

fn main() {}

}