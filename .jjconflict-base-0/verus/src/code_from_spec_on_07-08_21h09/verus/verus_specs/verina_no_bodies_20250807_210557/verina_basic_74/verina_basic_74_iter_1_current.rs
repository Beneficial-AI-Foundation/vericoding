use vstd::prelude::*;

verus! {

// Precondition: array must have at least one element
spec fn max_array_precond(a: &Vec<i32>) -> bool {
    a.len() > 0
}

// Spec version of the auxiliary function for use in specifications
spec fn max_array_aux_spec(a: &Vec<i32>, index: nat, current: i32) -> i32
    recommends
        index <= a.len(),
        a.len() > 0,
    decreases a.len() - index,
{
    if index < a.len() {
        let new_current = if current > a[index as int] { current } else { a[index as int] };
        max_array_aux_spec(a, index + 1, new_current)
    } else {
        current
    }
}

// Auxiliary recursive function to find maximum
fn max_array_aux(a: &Vec<i32>, index: usize, current: i32) -> (result: i32)
    requires
        index <= a.len(),
        a.len() > 0,
    ensures
        result == max_array_aux_spec(a, index as nat, current),
        // The result is at least as large as current
        result >= current,
        // The result is at least as large as any element from index onwards
        forall|k: int| index <= k < a.len() ==> result >= a[k],
        // The result equals some element in the array from index onwards, or equals current
        (exists|k: int| index <= k < a.len() && result == a[k]) || result == current,
    decreases a.len() - index,
{
    if index < a.len() {
        let new_current = if current > a[index] { current } else { a[index] };
        max_array_aux(a, index + 1, new_current)
    } else {
        current
    }
}

// Main function to find maximum element in array
fn max_array(a: &Vec<i32>) -> (result: i32)
    requires
        max_array_precond(a),
    ensures
        result == max_array_aux_spec(a, 1nat, a[0]),
        // Result is greater than or equal to all elements
        forall|k: int| 0 <= k < a.len() ==> result >= a[k],
        // Result equals some element in the array
        exists|k: int| 0 <= k < a.len() && result == a[k],
{
    max_array_aux(a, 1, a[0])
}

// Postcondition specification
spec fn max_array_postcond(a: &Vec<i32>, result: i32) -> bool 
    recommends max_array_precond(a)
{
    (forall|k: int| 0 <= k < a.len() ==> result >= a[k]) &&
    (exists|k: int| 0 <= k < a.len() && result == a[k])
}

// Theorem stating that max_array satisfies its postcondition
proof fn max_array_spec_satisfied(a: &Vec<i32>)
    requires 
        max_array_precond(a),
    ensures 
        max_array_postcond(a, max_array_aux_spec(a, 1nat, a[0]))
{
    // The proof is admitted for now (equivalent to sorry in Lean)
    admit();
}

}

fn main() {}