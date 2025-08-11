use vstd::prelude::*;

verus! {

// Precondition for containsConsecutiveNumbers
spec fn contains_consecutive_numbers_precond(a: &Vec<i32>) -> bool {
    true
}

// Postcondition for containsConsecutiveNumbers  
spec fn contains_consecutive_numbers_postcond(a: &Vec<i32>, result: bool) -> bool {
    (exists|i: int| 0 <= i < a.len() - 1 && a[i] + 1 == #[trigger] a[i + 1]) <==> result
}

// Main function that checks if array contains consecutive numbers
fn contains_consecutive_numbers(a: &Vec<i32>) -> (result: bool)
    requires contains_consecutive_numbers_precond(a)
    ensures contains_consecutive_numbers_postcond(a, result)
{
    return false;  // TODO: Remove this line and implement the function body
}

fn main() {}

} // verus!