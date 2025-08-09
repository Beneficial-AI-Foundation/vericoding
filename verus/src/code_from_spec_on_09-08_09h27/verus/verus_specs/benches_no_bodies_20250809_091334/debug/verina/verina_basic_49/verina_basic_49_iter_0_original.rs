use vstd::prelude::*;

verus! {

// Helper function to check if a number is odd
spec fn is_odd(x: int) -> bool {
    x % 2 != 0
}

// Precondition: array must be non-empty  
spec fn find_first_odd_precond(a: &Vec<i32>) -> bool {
    a.len() > 0
}

// Postcondition specification that matches the Lean version exactly
spec fn find_first_odd_postcond(a: &Vec<i32>, result: Option<usize>) -> bool {
    match result {
        Some(idx) => {
            &&& idx < a.len()
            &&& is_odd(a[idx as int] as int)  
            &&& forall|j: int| 0 <= j < idx ==> !is_odd(a[j] as int)
        }
        None => forall|i: int| 0 <= i < a.len() ==> !is_odd(a[i] as int)
    }
}

// Implementation function that finds the first odd element
fn find_first_odd(a: &Vec<i32>) -> (result: Option<usize>)
    requires find_first_odd_precond(a)
    ensures find_first_odd_postcond(a, result)
{
    return None;  // TODO: Remove this line and implement the function body
}

fn main() {}

} // verus!