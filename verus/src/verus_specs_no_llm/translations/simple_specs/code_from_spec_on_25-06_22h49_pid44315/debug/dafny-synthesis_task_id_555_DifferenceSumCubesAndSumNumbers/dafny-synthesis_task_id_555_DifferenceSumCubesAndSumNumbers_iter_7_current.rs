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
    ensures sum_numbers(n) * 2 == n * (n + 1)
    decreases n
{
    if n == 0 {
        assert(sum_numbers(0) == 0);
        assert(0 * 2 == 0 * (0 + 1));
    } else {
        lemma_sum_numbers_formula(n - 1);
        assert(sum_numbers(n) == n + sum_numbers(n - 1));
        assert(sum_numbers(n - 1) * 2 == (n - 1) * n);
        
        // Prove sum_numbers(n) * 2 == n * (n + 1)
        assert(sum_numbers(n) * 2 == (n + sum_numbers(n - 1)) * 2);
        assert((n + sum_numbers(n - 1)) * 2 == n * 2 + sum_numbers(n - 1) * 2);
        assert(n * 2 + sum_numbers(n - 1) * 2 == n * 2 + (n - 1) * n);
        assert(n * 2 + (n - 1) * n == 2 * n + n * n - n);
        assert(2 * n + n * n - n == n + n * n);
        assert(n + n * n == n * (1 + n));
        assert(n * (1 + n) == n * (n + 1));
    }
}

// Lemma to prove the formula for sum of cubes
proof fn lemma_sum_cubes_formula(n: int)
    requires n >= 0
    ensures sum_cubes(n) * 4 == n * n * (n + 1) * (n + 1)
    decreases n
{
    if n == 0 {
        assert(sum_cubes(0) == 0);
        assert(0 * 4 == 0 * 0 * (0 + 1) * (0 + 1));
    } else {
        lemma_sum_cubes_formula(n - 1);
        
        assert(sum_cubes(n) == n * n * n + sum_cubes(n - 1));
        assert(sum_cubes(n - 1) * 4 == (n - 1) * (n - 1) * n * n);
        
        // Prove sum_cubes(n) * 4 == n * n * (n + 1) * (n + 1)
        assert(sum_cubes(n) * 4 == (n * n * n + sum_cubes(n - 1)) * 4);
        assert((n * n * n + sum_cubes(n - 1)) * 4 == n * n * n * 4 + sum_cubes(n - 1) * 4);
        assert(n * n * n * 4 + sum_cubes(n - 1) * 4 == 4 * n * n * n + (n - 1) * (n - 1) * n * n);
        assert(4 * n * n * n + (n - 1) * (n - 1) * n * n == n * n * (4 * n + (n - 1) * (n - 1)));
        
        // Show that 4 * n + (n - 1) * (n - 1) == (n + 1) * (n + 1)
        assert(4 * n + (n - 1) * (n - 1) == 4 * n + (n * n - 2 * n + 1));
        assert(4 * n + (n * n - 2 * n + 1) == n * n + 2 * n + 1);
        assert(n * n + 2 * n + 1 == (n + 1) * (n + 1));
    }
}

// Helper function to compute sum of numbers
fn compute_sum_numbers(n: int) -> (result: int)
    requires n >= 0
    ensures result == sum_numbers(n)
    ensures result * 2 == n * (n + 1)
{
    proof {
        lemma_sum_numbers_formula(n);
    }
    (n * (n + 1)) / 2
}

// Helper function to compute sum of cubes
fn compute_sum_cubes(n: int) -> (result: int)
    requires n >= 0
    ensures result == sum_cubes(n)
    ensures result * 4 == n * n * (n + 1) * (n + 1)
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
        result * 4 == n * n * (n + 1) * (n + 1) - 2 * n * (n + 1)
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