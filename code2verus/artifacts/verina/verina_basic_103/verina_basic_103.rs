use vstd::prelude::*;

verus! {

// Precondition: array size must be at least 8
spec fn update_elements_precond(a: &Vec<i32>) -> bool {
    a.len() >= 8
}

// Postcondition: elements at indices 4 and 7 are updated correctly,
// and all other elements remain unchanged
spec fn update_elements_postcond(a: &Vec<i32>, result: &Vec<i32>) -> bool {
    &&& result.len() == a.len()
    &&& result[4] == a[4] + 3
    &&& result[7] == 516
    &&& forall|i: int| 0 <= i < a.len() && i != 4 && i != 7 ==> result[i] == a[i]
}

// Main function that updates elements at indices 4 and 7
fn update_elements(a: Vec<i32>) -> (result: Vec<i32>)
    requires 
        update_elements_precond(&a),
        a[4] < i32::MAX - 3,
        a[4] > i32::MIN
    ensures update_elements_postcond(&a, &result)
{
    let mut result = a;
    let old_val = result[4];
    result.set(4, old_val + 3);
    result.set(7, 516);
    result
}

}

fn main() {}