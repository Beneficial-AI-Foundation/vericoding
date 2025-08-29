use vstd::prelude::*;

verus! {

// Precondition: array must have at least one element
spec fn min_array_precond(a: &Vec<i32>) -> bool {
    a.len() > 0
}

// Helper function for the iterative search
fn find_min_loop(a: &Vec<i32>, i: usize, current_min: i32) -> (result: i32)
    requires
        a.len() > 0,
        i <= a.len(),
        exists|j: int| 0 <= j < a.len() && current_min == a[j as int],
        forall|j: int| 0 <= j < i ==> current_min <= a[j as int],
    ensures
        exists|k: int| 0 <= k < a.len() && result == a[k as int],
        forall|j: int| 0 <= j < a.len() ==> result <= a[j as int],
    decreases a.len() - i,
{
    if i < a.len() {
        let new_min = if current_min > a[i] { a[i] } else { current_min };
        assert(exists|k: int| 0 <= k < a.len() && new_min == a[k as int]);
        assert(forall|j: int| 0 <= j < i + 1 ==> new_min <= a[j as int]);
        find_min_loop(a, i + 1, new_min)
    } else {
        current_min
    }
}

// Main function to find minimum element in array
fn min_array(a: &Vec<i32>) -> (result: i32)
    requires
        min_array_precond(a),
    ensures
        // Result is less than or equal to all elements
        forall|i: int| 0 <= i < a.len() ==> result <= a[i as int],
        // Result exists in the array
        exists|i: int| 0 <= i < a.len() && result == a[i as int],
{
    find_min_loop(a, 1, a[0])
}

// Postcondition specification
spec fn min_array_postcond(a: &Vec<i32>, result: i32) -> bool {
    (forall|i: int| 0 <= i < a.len() ==> result <= a[i as int]) &&
    (exists|i: int| 0 <= i < a.len() && result == a[i as int])
}

}

fn main() {}