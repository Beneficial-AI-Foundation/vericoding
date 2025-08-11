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
    ensures result == spec_count_less_than(seq_to_int(numbers@), threshold as int)
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to fix termination verification */
    while i < numbers.len()
        invariant 
            i <= numbers.len(),
            count == spec_count_less_than(seq_to_int(numbers@.subrange(0, i as int)), threshold as int)
        decreases numbers.len() - i
    {
        if numbers[i] < threshold {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(numbers@.subrange(0, numbers.len() as int) =~= numbers@);
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
    /* code modified by LLM (iteration 1): removed println! macro as it's not supported in Verus */
    let numbers = vec![1, 5, 3, 8, 2];
    let threshold = 4;
    let result = CountLessThan(numbers, threshold);
}

} // verus!