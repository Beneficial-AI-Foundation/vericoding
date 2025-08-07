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
    let len = numbers.len();
    let mut idx = 0;
    
    while idx < len
        invariant 
            0 <= idx <= len,
            len == numbers.len(),
            has_close_elements_precond(numbers@, threshold),
        decreases len - idx,
    {
        let mut idx2 = 0;
        
        while idx2 < idx
            invariant 
                0 <= idx2 <= idx < len,
                len == numbers.len(),
                idx < numbers.len(),
                has_close_elements_precond(numbers@, threshold),
            decreases idx - idx2,
        {
            assert(idx2 < numbers.len());
            assert(idx < numbers.len());
            
            let a = numbers[idx2];
            let b = numbers[idx];
            
            // Use the precondition to establish bounds for abs_diff
            assert(numbers@[idx2 as int] >= -1000000 && numbers@[idx2 as int] <= 1000000);
            assert(numbers@[idx as int] >= -1000000 && numbers@[idx as int] <= 1000000);
            
            let d = abs_diff(a, b);
            
            if d < threshold {
                return true;
            }
            idx2 += 1;
        }
        idx += 1;
    }
    
    false
}

fn main() {
}

} // verus!