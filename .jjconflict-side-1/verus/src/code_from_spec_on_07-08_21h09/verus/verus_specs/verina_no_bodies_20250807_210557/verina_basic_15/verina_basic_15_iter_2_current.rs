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
    if a.len() < 2 {
        return false;
    }
    
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause to fix compilation error */
    while i < a.len() - 1
        invariant 
            0 <= i <= a.len() - 1,
            forall|j: int| 0 <= j < i ==> a[j] + 1 != a[j + 1]
        decreases a.len() - 1 - i
    {
        if a[i] + 1 == a[i + 1] {
            return true;
        }
        i += 1;
    }
    false
}

fn main() {}

} // verus!