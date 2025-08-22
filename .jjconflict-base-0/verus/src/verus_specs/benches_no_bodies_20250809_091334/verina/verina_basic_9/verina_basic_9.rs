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
    return false;  // TODO: Remove this line and implement the function body
}

}

fn main() {}