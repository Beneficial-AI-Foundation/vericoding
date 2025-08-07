use vstd::prelude::*;

verus! {

// Precondition function - matches the original Lean trivial precondition
pub open spec fn count_less_than_precond(numbers: Seq<int>, threshold: int) -> bool {
    true
}

// Specification function using fold - matches the Lean postcondition structure
pub open spec fn spec_count_less_than(numbers: Seq<int>, threshold: int) -> nat {
    numbers.fold_left(0nat, |count: nat, n: int| if n < threshold { count + 1 } else { count })
}

// Convert sequence of i32 to sequence of int for specification purposes
pub open spec fn seq_to_int(numbers: Seq<i32>) -> Seq<int> {
    numbers.map(|_idx: int, x: i32| x as int)
}

// Simple iterative implementation with bounds checking
pub fn count_less_than(numbers: Vec<i32>, threshold: i32) -> (result: usize)
    requires count_less_than_precond(seq_to_int(numbers@), threshold as int)
{
    return 0;  // TODO: Remove this line and implement the function body
}

// Postcondition function - matches the original Lean postcondition structure
// The original Lean had both result - fold = 0 and fold - result = 0, which means equality
pub open spec fn count_less_than_postcond(
    numbers: Seq<int>, 
    threshold: int, 
    result: usize, 
    h_precond: bool
) -> bool {
    h_precond ==> 
    (result == spec_count_less_than(numbers, threshold) && 
     spec_count_less_than(numbers, threshold) == result)
}

// Main wrapper function (matching the Lean signature)
pub fn CountLessThan(numbers: Vec<i32>, threshold: i32) -> (result: usize)
    requires count_less_than_precond(seq_to_int(numbers@), threshold as int)
    ensures count_less_than_postcond(seq_to_int(numbers@), threshold as int, result, count_less_than_precond(seq_to_int(numbers@), threshold as int))
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn main() {
    // TODO: Remove this comment and implement the function body
}

} // verus!