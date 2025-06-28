use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function for sum of numbers 1 to n
spec fn sum_numbers(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n + sum_numbers(n - 1) }
}

// Spec function for sum of cubes 1^3 to n^3
spec fn sum_cubes(n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { n * n * n + sum_cubes(n - 1) }
}

// Lemma to prove the formula for sum of numbers
proof fn lemma_sum_numbers_formula(n: int)
    requires n >= 0
    ensures sum_numbers(n) == (n * (n + 1)) / 2
    decreases n
{
    if n == 0 {
        assert(sum_numbers(0) == 0);
        assert((0 * (0 + 1)) / 2 == 0);
    } else {
        lemma_sum_numbers_formula(n - 1);
        assert(sum_numbers(n) == n + sum_numbers(n - 1));
        assert(sum_numbers(n - 1) == ((n - 1) * n) / 2);
        
        // Step by step algebraic manipulation
        assert(n + ((n - 1) * n) / 2 == (2 * n + (n - 1) * n) / 2);
        assert((2 * n + (n - 1) * n) / 2 == (2 * n + n * n - n) / 2);
        assert((2 * n + n * n - n) / 2 == (n + n * n) / 2);
        assert((n + n * n) / 2 == (n * (1 + n)) / 2);
        assert((n * (1 + n)) / 2 == (n * (n + 1)) / 2);
    }
}

// Lemma to prove the formula for sum of cubes
proof fn lemma_sum_cubes_formula(n: int)
    requires n >= 0
    ensures sum_cubes(n) == (n * n * (n + 1) * (n + 1)) / 4
    decreases n
{
    if n == 0 {
        assert(sum_cubes(0) == 0);
        assert((0 * 0 * (0 + 1) * (0 + 1)) / 4 == 0);
    } else {
        lemma_sum_cubes_formula(n - 1);
        
        assert(sum_cubes(n) == n * n * n + sum_cubes(n - 1));
        assert(sum_cubes(n - 1) == ((n - 1) * (n - 1) * n * n) / 4);
        
        // Algebraic manipulation
        assert(n * n * n + ((n - 1) * (n - 1) * n * n) / 4 == 
               (4 * n * n * n + (n - 1) * (n - 1) * n * n) / 4);
        assert((4 * n * n * n + (n - 1) * (n - 1) * n * n) / 4 == 
               (n * n * (4 * n + (n - 1) * (n - 1))) / 4);
        assert(4 * n + (n - 1) * (n - 1) == 4 * n + n * n - 2 * n + 1);
        assert(4 * n + n * n - 2 * n + 1 == n * n + 2 * n + 1);
        assert(n * n + 2 * n + 1 == (n + 1) * (n + 1));
        assert((n * n * (n + 1) * (n + 1)) / 4 == (n * n * (n + 1) * (n + 1)) / 4);
    }
}

// Helper function to compute sum of numbers iteratively
fn compute_sum_numbers(n: int) -> (result: int)
    requires n >= 0
    ensures result == sum_numbers(n)
    ensures result == (n * (n + 1)) / 2
{
    proof {
        lemma_sum_numbers_formula(n);
    }
    (n * (n + 1)) / 2
}

// Helper function to compute sum of cubes iteratively  
fn compute_sum_cubes(n: int) -> (result: int)
    requires n >= 0
    ensures result == sum_cubes(n)
    ensures result == (n * n * (n + 1) * (n + 1)) / 4
{
    proof {
        lemma_sum_cubes_formula(n);
    }
    (n * n * (n + 1) * (n + 1)) / 4
}

fn DifferenceSumCubesAndSumNumbers(n: int) -> (result: int)
    requires
        n >= 0
    ensures
        result == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
    proof {
        lemma_sum_cubes_formula(n);
        lemma_sum_numbers_formula(n);
    }
    
    let sum_cubes_val = compute_sum_cubes(n);
    let sum_numbers_val = compute_sum_numbers(n);
    
    sum_cubes_val - sum_numbers_val
}

}