use vstd::prelude::*;

verus! {

// Precondition: both arrays must be non-empty
spec fn has_common_element_precond(a: Seq<i32>, b: Seq<i32>) -> bool {
    a.len() > 0 && b.len() > 0
}

// Postcondition: result is true iff there exist indices where elements are equal
spec fn has_common_element_postcond(a: Seq<i32>, b: Seq<i32>, result: bool) -> bool {
    (exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j]) <==> result
}

// Implementation function
fn has_common_element(a: &Vec<i32>, b: &Vec<i32>) -> (result: bool)
    requires
        has_common_element_precond(a@, b@),
    ensures
        has_common_element_postcond(a@, b@, result),
{
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < b@.len() ==> a@[k] != b@[j],
        decreases a.len() - i,
    {
        let mut j = 0;
        while j < b.len()
            invariant
                i < a.len(),
                j <= b.len(),
                forall|k: int, l: int| 0 <= k < i && 0 <= l < b@.len() ==> a@[k] != b@[l],
                forall|l: int| 0 <= l < j ==> a@[i as int] != b@[l],
            decreases b.len() - j,
        {
            if a[i] == b[j] {
                assert(a@[i as int] == b@[j as int]);
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    // If we get here, no common element was found
    assert(forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < b@.len() ==> a@[i] != b@[j]);
    false
}

}

fn main() {}