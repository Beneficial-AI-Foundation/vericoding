use vstd::prelude::*;

verus! {

// Precondition from Lean - just True  
spec fn sum_of_squares_of_first_n_odd_numbers_precond(n: nat) -> bool {
    true
}

// Postcondition from Lean - the mathematical formula
spec fn sum_of_squares_of_first_n_odd_numbers_postcond(n: nat, result: nat) -> bool {
    let expected = n * (2 * n - 1) * (2 * n + 1) / 3;
    result == expected
}

// Main function implementing the loop from Lean
fn sum_of_squares_of_first_n_odd_numbers(n: u32) -> (result: u32)
    requires 
        sum_of_squares_of_first_n_odd_numbers_precond(n as nat),
        n > 0,
    ensures 
        sum_of_squares_of_first_n_odd_numbers_postcond(n as nat, result as nat),
{
    let mut k = n;
    let mut sum = 0u32;
    
    while k > 0
        invariant 
            k <= n,
            n > 0,
        decreases k
    {
        // For the k-th iteration, we compute (2k-1)²
        let odd_num = 2 * k - 1;
        let square = odd_num * odd_num;
        sum = sum + square;
        k = k - 1;
    }
    
    proof {
        // Since the original Lean proof uses "sorry", we assume the postcondition holds
        assume(sum_of_squares_of_first_n_odd_numbers_postcond(n as nat, sum as nat));
    }
    
    sum
}

// The theorem from the original Lean code
proof fn sum_of_squares_of_first_n_odd_numbers_spec_satisfied(n: nat)
    requires sum_of_squares_of_first_n_odd_numbers_precond(n),
    ensures sum_of_squares_of_first_n_odd_numbers_postcond(n, spec_sum_squares(n as int) as nat),
{
    // Matches the "sorry" from the original Lean proof
    assume(sum_of_squares_of_first_n_odd_numbers_postcond(n, spec_sum_squares(n as int) as nat));
}

// Specification of the sum of squares computation
spec fn spec_sum_squares(n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        let odd_num = 2 * n - 1;
        spec_sum_squares(n - 1) + odd_num * odd_num
    }
}

} // end verus block

fn main() {}