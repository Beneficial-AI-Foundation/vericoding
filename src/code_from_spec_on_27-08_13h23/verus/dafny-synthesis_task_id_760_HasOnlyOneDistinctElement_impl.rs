use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to check if all elements in a slice are equal to a given value
proof fn all_elements_equal(a: &[i32], start: int, value: i32)
    requires
        0 <= start <= a.len() as int,
    ensures
        (forall|i: int| start <= i < a.len() ==> a[i] == value) ==> 
        (forall|i: int, j: int| start <= i < a.len() && start <= j < a.len() ==> a[i] == a[j]),
{
    // No additional proof needed, follows from the definition
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    ensures 
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn has_only_one_distinct_element(a: &[i32]) -> (result: bool)
    ensures 
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j],
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] != a[j],
{
    if a.len() == 0 {
        return true;
    }
    
    let first = a[0];
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i as int ==> a[j] == first,
    {
        if a[i] != first {
            return false;
        }
        i = i + 1;
    }
    
    proof {
        all_elements_equal(a, 0, first);
    }
    
    true
}
// </vc-code>

fn main() {}

}