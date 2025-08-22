use vstd::prelude::*;

verus! {

// Helper function to check if a number is odd
spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

// Precondition - always true in this case  
spec fn is_odd_at_index_odd_precond(a: Seq<i32>) -> bool {
    true
}

// Postcondition specification
spec fn is_odd_at_index_odd_postcond(a: Seq<i32>, result: bool) -> bool {
    result == (forall|i: int| #![auto] 0 <= i < a.len() && is_odd(i) ==> is_odd(a[i] as int))
}

// Main function that checks if all elements at odd indices are odd numbers
// This translates the Lean function that creates indexed pairs and uses Array.all
fn is_odd_at_index_odd(a: &Vec<i32>) -> (result: bool)
    requires is_odd_at_index_odd_precond(a@) 
{
    return false;  // TODO: Remove this line and implement the function body
}

fn main() {}

}