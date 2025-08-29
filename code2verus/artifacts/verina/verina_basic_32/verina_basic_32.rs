use vstd::prelude::*;

verus! {

// Precondition: array must have at least one element
spec fn swap_first_and_last_precond(a: &Vec<i32>) -> bool {
    a.len() > 0
}

// Postcondition specification matching the original Lean postcondition
spec fn swap_first_and_last_postcond(a: &Vec<i32>, result: &Vec<i32>) -> bool {
    &&& result.len() == a.len()
    &&& result[0] == a[a.len() - 1]
    &&& result[result.len() - 1] == a[0]
    &&& forall|i: int| 1 <= i <= (result.len() - 2) ==> result[i] == a[i]
}

// Main function that swaps first and last elements
fn swap_first_and_last(a: &Vec<i32>) -> (result: Vec<i32>)
    requires
        swap_first_and_last_precond(a),
    ensures
        swap_first_and_last_postcond(a, &result),
{
    let mut result = a.clone();
    let first = a[0];
    let last = a[a.len() - 1];
    
    result.set(0, last);
    result.set((a.len() - 1) as usize, first);
    
    result
}

}

fn main() {}