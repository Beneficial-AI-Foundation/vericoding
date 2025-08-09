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
    let mut result = Vec::new();
    
    // Handle the case where there's only one element
    if a.len() == 1 {
        result.push(a[0]);
        return result;
    }
    
    // For arrays with 2 or more elements, swap first and last
    let first = a[0];
    let last = a[a.len() - 1];
    
    // Build the result vector
    result.push(last);  // Put last element first
    
    // Copy middle elements
    let mut i = 1;
    /* code modified by LLM (iteration 1): added decreases clause to satisfy verification requirement */
    while i < a.len() - 1
        invariant
            result.len() == i,
            i <= a.len() - 1,
            a.len() > 1,
            result[0] == a[a.len() - 1],
            forall|j: int| 1 <= j < i ==> result[j] == a[j],
        decreases a.len() - i
    {
        result.push(a[i]);
        i += 1;
    }
    
    // Put first element last
    result.push(first);
    
    result
}

}

fn main() {}