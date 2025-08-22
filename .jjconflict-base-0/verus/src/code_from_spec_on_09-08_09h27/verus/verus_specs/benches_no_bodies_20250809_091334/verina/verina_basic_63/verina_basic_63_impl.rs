use vstd::prelude::*;

verus! {

// Helper function to compute absolute difference for integers
fn abs_diff(a: i32, b: i32) -> (result: i32) 
    requires 
        a >= -1000000 && a <= 1000000,
        b >= -1000000 && b <= 1000000,
    ensures result >= 0,
{
    if a >= b {
        a - b
    } else {
        b - a
    }
}

// Precondition - threshold is non-negative and all numbers are within bounds
spec fn has_close_elements_precond(numbers: Seq<i32>, threshold: i32) -> bool {
    threshold >= 0 &&
    forall|i: int| 0 <= i < numbers.len() ==> 
        numbers[i] >= -1000000 && numbers[i] <= 1000000
}

// Main function implementation matching the Lean nested loop structure
fn has_close_elements(numbers: Vec<i32>, threshold: i32) -> (result: bool)
    requires has_close_elements_precond(numbers@, threshold),
{
    let n = numbers.len();
    
    for i in 0..n
        invariant has_close_elements_precond(numbers@, threshold),
    {
        for j in (i + 1)..n
            invariant 
                has_close_elements_precond(numbers@, threshold),
                i < n,
        {
            let diff = abs_diff(numbers[i], numbers[j]);
            if diff <= threshold {
                return true;
            }
        }
    }
    
    false
}

fn main() {
}

} // verus!