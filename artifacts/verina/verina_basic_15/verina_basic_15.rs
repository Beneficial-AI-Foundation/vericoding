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
    if a.len() <= 1 {
        assert(!(exists|i: int| 0 <= i < a.len() - 1 && a[i] + 1 == #[trigger] a[i + 1]));
        false
    } else {
        let mut idx: usize = 0;
        
        while idx < a.len() - 1
            invariant 
                0 <= idx <= a.len() - 1,
                a.len() >= 2,
                forall|i: int| 0 <= i < idx ==> a[i] + 1 != #[trigger] a[i + 1]
            decreases a.len() - 1 - idx
        {
            // Handle potential overflow
            if a[idx] != i32::MAX && a[idx] + 1 == a[idx + 1] {
                // Found consecutive numbers
                assert(0 <= idx < a.len() - 1);
                assert(a[idx as int] + 1 == a[(idx + 1) as int]);
                assert(exists|i: int| 0 <= i < a.len() - 1 && a[i] + 1 == #[trigger] a[i + 1]) by {
                    assert(a[idx as int] + 1 == a[(idx + 1) as int]);
                }
                return true;
            }
            idx += 1;
        }
        
        // If we reach here, no consecutive numbers were found
        assert(idx == a.len() - 1);
        assert(forall|i: int| 0 <= i < a.len() - 1 ==> a[i] + 1 != #[trigger] a[i + 1]);
        assert(!(exists|i: int| 0 <= i < a.len() - 1 && a[i] + 1 == #[trigger] a[i + 1]));
        false
    }
}

fn main() {}

} // verus!