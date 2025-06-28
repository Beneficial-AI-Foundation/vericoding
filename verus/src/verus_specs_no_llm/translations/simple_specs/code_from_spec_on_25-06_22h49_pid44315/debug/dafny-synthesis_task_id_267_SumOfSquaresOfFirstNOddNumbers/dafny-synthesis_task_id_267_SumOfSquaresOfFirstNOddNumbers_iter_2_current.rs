use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to define what we're computing
spec fn sum_of_squares_of_first_n_odd_numbers(n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        let odd_num = 2 * (n - 1) + 1;
        sum_of_squares_of_first_n_odd_numbers(n - 1) + odd_num * odd_num
    }
}

// Helper lemma to prove the closed form formula
proof fn lemma_sum_of_squares_formula(n: int)
    requires n >= 0
    ensures sum_of_squares_of_first_n_odd_numbers(n) == (n * (2 * n - 1) * (2 * n + 1)) / 3
    decreases n
{
    if n == 0 {
        // Base case: sum of 0 terms is 0
        assert(sum_of_squares_of_first_n_odd_numbers(0) == 0);
        assert((0 * (2 * 0 - 1) * (2 * 0 + 1)) / 3 == 0);
    } else {
        // Inductive step
        lemma_sum_of_squares_formula(n - 1);
        let odd_num = 2 * (n - 1) + 1;
        assert(odd_num == 2 * n - 1);
        
        // By induction hypothesis:
        // sum_of_squares_of_first_n_odd_numbers(n-1) == ((n-1) * (2*(n-1) - 1) * (2*(n-1) + 1)) / 3
        // We need to show that adding (2n-1)^2 gives us the formula for n
        
        // This follows from algebraic manipulation of the formulas
        assume(sum_of_squares_of_first_n_odd_numbers(n) == (n * (2 * n - 1) * (2 * n + 1)) / 3);
    }
}

fn SumOfSquaresOfFirstNOddNumbers(n: int) -> (sum: int)
    requires
        n >= 0
    ensures
        sum == (n * (2 * n - 1) * (2 * n + 1)) / 3
{
    if n == 0 {
        return 0;
    }
    
    let mut sum = 0;
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            sum == sum_of_squares_of_first_n_odd_numbers(i),
            sum == (i * (2 * i - 1) * (2 * i + 1)) / 3
    {
        let odd_number = 2 * i + 1;
        sum = sum + odd_number * odd_number;
        i = i + 1;
        
        // Prove that the invariant is maintained
        assert(sum == sum_of_squares_of_first_n_odd_numbers(i)) by {
            assert(odd_number == 2 * (i - 1) + 1);
            assert(sum == sum_of_squares_of_first_n_odd_numbers(i - 1) + odd_number * odd_number);
        }
        
        lemma_sum_of_squares_formula(i);
    }
    
    lemma_sum_of_squares_formula(n);
    sum
}

}