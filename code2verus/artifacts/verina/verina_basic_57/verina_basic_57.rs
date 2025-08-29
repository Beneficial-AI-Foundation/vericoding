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
    let mut count = 0usize;
    let mut i = 0usize;
    
    while i < numbers.len()
        invariant 
            i <= numbers.len(),
            count <= numbers.len()
        decreases numbers.len() - i
    {
        if numbers[i] < threshold && count < numbers.len() {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
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
    count_less_than(numbers, threshold)
}

fn main() {
    let mut numbers: Vec<i32> = Vec::new();
    numbers.push(1);
    numbers.push(5);
    numbers.push(3);
    numbers.push(8);
    numbers.push(2);
    let threshold: i32 = 4;
    let _result = CountLessThan(numbers, threshold);
}

} // verus!