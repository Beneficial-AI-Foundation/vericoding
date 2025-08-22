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
    let mut sum = 0u32;
    let mut i = 1u32;
    
    /* code modified by LLM (iteration 1): Added decreases clause for loop termination */
    while i <= n
        invariant
            1 <= i <= n + 1,
            sum == spec_sum_squares(i as int - 1),
        decreases n - i + 1,
    {
        let odd_num = 2 * i - 1;
        sum = sum + odd_num * odd_num;
        i = i + 1;
    }
    
    proof {
        lemma_sum_squares_formula(n as int);
    }
    
    sum
}

// The theorem from the original Lean code
proof fn sum_of_squares_of_first_n_odd_numbers_spec_satisfied(n: nat)
    requires sum_of_squares_of_first_n_odd_numbers_precond(n),
    ensures sum_of_squares_of_first_n_odd_numbers_postcond(n, spec_sum_squares(n as int) as nat),
{
    lemma_sum_squares_formula(n as int);
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

// Lemma proving the mathematical formula
proof fn lemma_sum_squares_formula(n: int)
    requires n >= 0,
    ensures spec_sum_squares(n) == n * (2 * n - 1) * (2 * n + 1) / 3,
    decreases n,
{
    if n == 0 {
        // Base case: spec_sum_squares(0) = 0 = 0 * (-1) * 1 / 3
        assert(spec_sum_squares(0) == 0);
        assert(0 * (2 * 0 - 1) * (2 * 0 + 1) / 3 == 0);
    } else {
        // Inductive step
        lemma_sum_squares_formula(n - 1);
        
        // spec_sum_squares(n) = spec_sum_squares(n-1) + (2*n-1)^2
        // By IH: spec_sum_squares(n-1) = (n-1) * (2*(n-1)-1) * (2*(n-1)+1) / 3
        //                               = (n-1) * (2*n-3) * (2*n-1) / 3
        
        let prev_sum = (n - 1) * (2 * (n - 1) - 1) * (2 * (n - 1) + 1) / 3;
        let odd_square = (2 * n - 1) * (2 * n - 1);
        let current_sum = prev_sum + odd_square;
        let expected = n * (2 * n - 1) * (2 * n + 1) / 3;
        
        // Algebraic manipulation to show they're equal
        assert(prev_sum == (n - 1) * (2 * n - 3) * (2 * n - 1) / 3);
        
        // Expand the expected formula
        assert(expected == n * (2 * n - 1) * (2 * n + 1) / 3);
        
        // The algebraic proof would show:
        // (n-1) * (2*n-3) * (2*n-1) / 3 + (2*n-1)^2 = n * (2*n-1) * (2*n+1) / 3
        
        // For Verus verification, we can use the mathematical fact
        assert(current_sum == expected) by(nonlinear_arith);
        assert(spec_sum_squares(n) == expected);
    }
}

} // end verus block

fn main() {}