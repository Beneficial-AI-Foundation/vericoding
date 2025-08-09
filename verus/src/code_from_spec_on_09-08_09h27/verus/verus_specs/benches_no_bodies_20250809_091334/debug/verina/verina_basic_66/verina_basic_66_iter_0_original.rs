use vstd::prelude::*;

verus! {

// Precondition - always true
spec fn compute_is_even_precond(x: int) -> bool {
    true
}

// The main function that computes if x is even
fn compute_is_even(x: i32) -> (result: bool)
    requires compute_is_even_precond(x as int),
    ensures result == true <==> exists|k: int| #[trigger] (2 * k) == (x as int),
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}